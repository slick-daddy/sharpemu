// Copyright (C) 2026 SharpEmu Emulator Project
// SPDX-License-Identifier: GPL-2.0-or-later

using SharpEmu.HLE;
using SharpEmu.Libs.Ampr;
using SharpEmu.Libs.Bink;
using System.Buffers;
using System.Buffers.Binary;
using System.Collections.Concurrent;
using System.Text;
using System.Threading;
using System.Runtime.InteropServices;
using System.Linq;
using System.Globalization;
using SharpEmu.Logging;

namespace SharpEmu.Libs.Kernel;

public static partial class KernelMemoryCompatExports
{
    private static readonly SharpEmuLogger Log = SharpEmuLog.For("Libs.Kernel");
    private const int MaxGuestStringLength = 4096;
    private const int WideCharSize = sizeof(ushort);
    private const int MemsetChunkSize = 16 * 1024;
    private static readonly byte[] _zeroChunk = new byte[MemsetChunkSize];
    private const int O_WRONLY = 0x1;
    private const int O_RDWR = 0x2;
    private const int O_APPEND = 0x8;
    private const int O_CREAT = 0x0200;
    private const int O_TRUNC = 0x0400;
    private const int O_DIRECTORY = 0x00020000;
    private const int OrbisKernelMapFixed = 0x0010;
    private const int OrbisKernelMapOpMapDirect = 0;
    private const int OrbisKernelMapOpUnmap = 1;
    private const int OrbisKernelMapOpProtect = 2;
    private const int OrbisKernelMapOpMapFlexible = 3;
    private const int OrbisKernelMapOpTypeProtect = 4;
    private const int OrbisKernelBatchMapEntrySize = 32;
    private const int OrbisKernelBatchMapEntryStartOffset = 0;
    private const int OrbisKernelBatchMapEntryOffsetOffset = 8;
    private const int OrbisKernelBatchMapEntryLengthOffset = 16;
    private const int OrbisKernelBatchMapEntryProtectionOffset = 24;
    private const int OrbisKernelBatchMapEntryTypeOffset = 25;
    private const int OrbisKernelBatchMapEntryOperationOffset = 28;
    private const ulong OrbisPageSize = 0x4000;
    private const int OrbisProtCpuRead = 0x01;
    private const int OrbisProtCpuWrite = 0x02;
    private const int OrbisProtCpuExec = 0x04;
    private const int OrbisProtGpuRead = 0x10;
    private const int OrbisProtGpuWrite = 0x20;
    private const int OrbisProtCpuReadWrite = OrbisProtCpuRead | OrbisProtCpuWrite;
    private const int SeekSet = 0;
    private const int SeekCur = 1;
    private const int SeekEnd = 2;
    private const ulong DirectMemorySizeBytes = 16384UL * 1024 * 1024;
    private const ulong UnsetMainDirectMemoryPoolBase = ulong.MaxValue;
    private const ulong FlexibleMemorySizeBytes = 448UL * 1024 * 1024;
    private const int OrbisVirtualQueryInfoSize = 72;
    private const int OrbisKernelMaximumNameLength = 32;
    private const uint MemCommit = 0x1000;
    private const uint HostPageNoAccess = 0x01;
    private const uint HostPageReadOnly = 0x02;
    private const uint HostPageReadWrite = 0x04;
    private const uint HostPageWriteCopy = 0x08;
    private const uint HostPageExecute = 0x10;
    private const uint HostPageExecuteRead = 0x20;
    private const uint HostPageExecuteReadWrite = 0x40;
    private const uint HostPageExecuteWriteCopy = 0x80;
    private const uint HostPageGuard = 0x100;
    private const int Enomem = 12;
    private const int Efault = 14;
    private const int Einval = 22;
    private const int Erange = 34;
    private const int Struncate = 80;
    private const nuint DefaultLibcHeapAlignment = 16;
    private const ushort KernelStatModeDirectory = 0x41FF;
    private const ushort KernelStatModeRegular = 0x81FF;
    private const int KernelStatSize = 120;
    private const int KernelStatStDevOffset = 0;
    private const int KernelStatStInoOffset = 4;
    private const int KernelStatStModeOffset = 8;
    private const int KernelStatStNlinkOffset = 10;
    private const int KernelStatStUidOffset = 12;
    private const int KernelStatStGidOffset = 16;
    private const int KernelStatStRdevOffset = 20;
    private const int KernelStatStAtimOffset = 24;
    private const int KernelStatStMtimOffset = 40;
    private const int KernelStatStCtimOffset = 56;
    private const int KernelStatStSizeOffset = 72;
    private const int KernelStatStBlocksOffset = 80;
    private const int KernelStatStBlksizeOffset = 88;
    private const int KernelStatStFlagsOffset = 92;
    private const int KernelStatStGenOffset = 96;
    private const int KernelStatStLspareOffset = 100;
    private const int KernelStatStBirthtimOffset = 104;

    private static readonly object _fdGate = new();
    private static readonly Dictionary<int, FileStream> _openFiles = new();
    private static readonly Dictionary<int, OpenDirectory> _openDirectories = new();
    private static readonly object _libcAllocGate = new();
    private static readonly object _memoryGate = new();
    private static readonly object _ioTraceGate = new();
    private static readonly object _statCacheGate = new();
    private static readonly object _guestMountGate = new();
    private static readonly Dictionary<ulong, DirectAllocation> _directAllocations = new();
    private static readonly Dictionary<ulong, LibcHeapAllocation> _libcAllocations = new();
    private static readonly SortedList<ulong, MappedRegion> _mappedRegions = new();
    private static readonly Dictionary<ulong, string> _mappedRegionNames = new();
    private static readonly Dictionary<string, string> _guestMounts = new(StringComparer.OrdinalIgnoreCase);
    private static readonly HashSet<string> _tracedStatResults = new(StringComparer.Ordinal);
    private static readonly HashSet<string> _negativeStatCache = new(StringComparer.OrdinalIgnoreCase);
    private static readonly ConcurrentDictionary<string, ulong> _aprFileSizeCache = new(StringComparer.OrdinalIgnoreCase);
    private static long _nextFileDescriptor = 2;

    internal static int AllocateGuestFileDescriptor()
    {
        lock (_fdGate)
        {
            return (int)Interlocked.Increment(ref _nextFileDescriptor);
        }
    }

    private static ulong _nextPhysicalAddress;
    private static ulong _nextVirtualAddress;
    private static readonly ulong DefaultMapSearchBase =
        OperatingSystem.IsWindows() ? 0x1_0000_0000UL : 0x20_0000_0000UL;
    private static ulong _mainDirectMemoryPoolBase = UnsetMainDirectMemoryPoolBase;
    private static ulong _allocatedFlexibleBytes;
    private static ulong _threadAtexitCountCallback;
    private static ulong _threadAtexitReportCallback;
    private static ulong _threadDtorsCallback;
    private static int _nullMemsetRecoveryCount;
    private static int _nonCanonicalMemsetRecoveryCount;
    private static int _inaccessibleMemsetRecoveryCount;
    private static int _hostMemoryWriteFallbackCount;
    private static int _hostMemoryReadFallbackCount;
    private static int _nullWcscpyRecoveryCount;
    private static int _nullStrcasecmpRecoveryCount;
    private static string? _cachedApp0Root;
    private static string? _cachedDownload0Root;

    [StructLayout(LayoutKind.Sequential)]
    private struct MemoryBasicInformation
    {
        public nint BaseAddress;
        public nint AllocationBase;
        public uint AllocationProtect;
        public nuint RegionSize;
        public uint State;
        public uint Protect;
        public uint Type;
    }

    private static unsafe nuint VirtualQuery(nint lpAddress, out MemoryBasicInformation lpBuffer, nuint dwLength)
    {
        _ = dwLength;
        var result = HostMemory.Query((void*)lpAddress, out var info);
        lpBuffer = default;
        lpBuffer.BaseAddress = (nint)info.BaseAddress;
        lpBuffer.AllocationBase = (nint)info.AllocationBase;
        lpBuffer.AllocationProtect = info.AllocationProtect;
        lpBuffer.RegionSize = (nuint)info.RegionSize;
        lpBuffer.State = info.State;
        lpBuffer.Protect = info.Protect;
        lpBuffer.Type = info.Type;
        return result;
    }

    private static unsafe bool VirtualProtect(nint lpAddress, nuint dwSize, uint flNewProtect, out uint lpflOldProtect) =>
        HostMemory.Protect((void*)lpAddress, dwSize, flNewProtect, out lpflOldProtect);

    private sealed class OpenDirectory
    {
        public required string Path { get; init; }
        public required string[] Entries { get; init; }
        public int NextIndex { get; set; }
    }

    private readonly record struct DirectAllocation(ulong Start, ulong Length, int MemoryType);
    private readonly record struct LibcHeapAllocation(nint BaseAddress, nuint Size, nuint Alignment);
    private readonly record struct MappedRegion(ulong Address, ulong Length, int Protection, bool IsFlexible, bool IsDirect, ulong DirectStart);
    private readonly record struct BatchMapEntry(ulong Start, ulong Offset, ulong Length, byte Protection, byte Type, int Operation);

    public static void RegisterGuestPathMount(string guestMountPoint, string hostRoot)
    {
        ArgumentException.ThrowIfNullOrWhiteSpace(guestMountPoint);
        ArgumentException.ThrowIfNullOrWhiteSpace(hostRoot);

        var normalizedMountPoint = NormalizeGuestStatCachePath(guestMountPoint);
        if (normalizedMountPoint is null || normalizedMountPoint == "/")
        {
            throw new ArgumentException("Guest mount point must name a directory.", nameof(guestMountPoint));
        }

        var normalizedHostRoot = Path.GetFullPath(hostRoot);
        Directory.CreateDirectory(normalizedHostRoot);
        lock (_guestMountGate)
        {
            _guestMounts[normalizedMountPoint] = normalizedHostRoot;
        }

        lock (_statCacheGate)
        {
            _negativeStatCache.RemoveWhere(path =>
                string.Equals(path, normalizedMountPoint, StringComparison.OrdinalIgnoreCase) ||
                path.StartsWith(normalizedMountPoint + "/", StringComparison.OrdinalIgnoreCase));
        }
    }

    internal static bool TryAllocateHleData(
        CpuContext ctx,
        ulong length,
        ulong alignment,
        out ulong address)
    {
        address = 0;
        if (length == 0 || length > int.MaxValue)
        {
            return false;
        }

        var mappedLength = AlignUp(length, 0x1000UL);
        var effectiveAlignment = Math.Max(alignment, 0x1000UL);
        lock (_memoryGate)
        {
            var desiredAddress = AlignUp(
                _nextVirtualAddress == 0 ? DefaultMapSearchBase : _nextVirtualAddress,
                effectiveAlignment);
            if (!TryReserveGuestVirtualRange(ctx, desiredAddress, mappedLength, OrbisProtCpuReadWrite, effectiveAlignment, out address) ||
                address == 0)
            {
                return false;
            }

            _nextVirtualAddress = Math.Max(_nextVirtualAddress, address + mappedLength);
            _mappedRegions[address] = new MappedRegion(
                address,
                mappedLength,
                OrbisProtCpuReadWrite,
                IsFlexible: false,
                IsDirect: false,
                DirectStart: 0);
        }

        for (ulong offset = 0; offset < mappedLength;)
        {
            var chunkLength = (int)Math.Min((ulong)_zeroChunk.Length, mappedLength - offset);
            if (!ctx.Memory.TryWrite(address + offset, _zeroChunk.AsSpan(0, chunkLength)))
            {
                return false;
            }

            offset += (ulong)chunkLength;
        }

        return true;
    }

    private static ulong _dummyVtableAddress;
    private const int DummyVtableSlotCount = 64;

    internal static bool TryWriteDummyVtable(CpuContext ctx, ulong objectAddress)
    {
        if (objectAddress == 0 || !TryEnsureDummyVtable(ctx, out var vtableAddress))
        {
            return false;
        }

        return ctx.TryWriteUInt64(objectAddress, vtableAddress);
    }

    private static bool TryEnsureDummyVtable(CpuContext ctx, out ulong vtableAddress)
    {
        lock (_memoryGate)
        {
            if (_dummyVtableAddress != 0)
            {
                vtableAddress = _dummyVtableAddress;
                return true;
            }

            const int executableReadWrite = OrbisProtCpuRead | OrbisProtCpuWrite | OrbisProtCpuExec;
            if (!TryAllocateHleData(ctx, 0x1000, 0x1000, executableReadWrite, out var block))
            {
                vtableAddress = 0;
                return false;
            }

            // xor eax, eax; ret - every dummy virtual method just returns 0 and does nothing else.
            if (!ctx.Memory.TryWrite(block, new byte[] { 0x31, 0xC0, 0xC3 }))
            {
                vtableAddress = 0;
                return false;
            }

            var table = new byte[DummyVtableSlotCount * sizeof(ulong)];
            for (var i = 0; i < DummyVtableSlotCount; i++)
            {
                BinaryPrimitives.WriteUInt64LittleEndian(table.AsSpan(i * sizeof(ulong), sizeof(ulong)), block);
            }

            var tableAddress = block + 0x100;
            if (!ctx.Memory.TryWrite(tableAddress, table))
            {
                vtableAddress = 0;
                return false;
            }

            Log.Info($"Dummy vtable ready: stub=0x{block:X16} vtable=0x{tableAddress:X16} slots={DummyVtableSlotCount}");
            _dummyVtableAddress = tableAddress;
            vtableAddress = tableAddress;
            return true;
        }
    }

    internal static void RegisterReservedVirtualRange(ulong address, ulong length)
    {
        if (address == 0 || length == 0)
        {
            return;
        }

        lock (_memoryGate)
        {
            _mappedRegions[address] = new MappedRegion(
                address,
                length,
                Protection: 0,
                IsFlexible: false,
                IsDirect: false,
                DirectStart: 0);
        }
    }

    [SysAbiExport(
        Nid = "8zTFvBIAIN8",
        ExportName = "memset",
        Target = Generation.Gen4 | Generation.Gen5,
        LibraryName = "libc")]
    public static int Memset(CpuContext ctx)
    {
        var destination = ctx[CpuRegister.Rdi];
        var value = (byte)(ctx[CpuRegister.Rsi] & 0xFF);
        var length = ctx[CpuRegister.Rdx];
        if (length == 0)
        {
            ctx[CpuRegister.Rax] = destination;
            return (int)OrbisGen2Result.ORBIS_GEN2_OK;
        }

        if (destination == 0)
        {
            if (length <= 0x20)
            {
                var recoveryIndex = Interlocked.Increment(ref _nullMemsetRecoveryCount);
                if (recoveryIndex <= 8)
                {
                    Log.Warn($"memset null-dst recovery#{recoveryIndex}: rip=0x{ctx.Rip:X16} len=0x{length:X} val=0x{value:X2}");
                }

                ctx[CpuRegister.Rax] = 0;
                return (int)OrbisGen2Result.ORBIS_GEN2_OK;
            }

            // Longer null-dst memsets are unrecoverable, but RAX must still be set - leaving it
            // stale here previously let callers that do `buf = memset(...)` carry on with a
            // garbage "buffer" pointer instead of a clean NULL, causing a *different*,
            // confusingly-located crash further downstream.
            var largeRecoveryIndex = Interlocked.Increment(ref _nullMemsetRecoveryCount);
            if (largeRecoveryIndex <= 8)
            {
                Log.Warn($"memset null-dst (len>0x20) recovery#{largeRecoveryIndex}: rip=0x{ctx.Rip:X16} len=0x{length:X} val=0x{value:X2}");
            }

            ctx[CpuRegister.Rax] = 0;
            return (int)OrbisGen2Result.ORBIS_GEN2_ERROR_INVALID_ARGUMENT;
        }

        const ulong CanonicalUserUpper = 0x0000800000000000UL;
        if (destination >= CanonicalUserUpper && length <= 0x40)
        {
            var recoveryIndex = Interlocked.Increment(ref _nonCanonicalMemsetRecoveryCount);
            if (recoveryIndex <= 8)
            {
                Log.Warn($"memset non-canonical-dst recovery#{recoveryIndex}: rip=0x{ctx.Rip:X16} dst=0x{destination:X16} len=0x{length:X} val=0x{value:X2}");
            }

            ctx[CpuRegister.Rax] = destination;
            return (int)OrbisGen2Result.ORBIS_GEN2_OK;
        }

        const ulong MaxSane = 2UL * 1024 * 1024 * 1024;
        if (destination < 0x1000 || destination >= CanonicalUserUpper || length > MaxSane)
        {
            Console.WriteLine("!!! CRITICAL: Bad Memset Call !!!");
            Console.WriteLine($"Called from RIP: 0x{ctx.Rip:X}");
            Console.WriteLine($"dst=0x{destination:X} val=0x{value:X2} len=0x{length:X}");
            return (int)OrbisGen2Result.ORBIS_GEN2_ERROR_MEMORY_FAULT;
        }

        // Rent may hand back a larger array than requested; only the first chunkLength
        // bytes are filled, so the loop must cap at chunkLength rather than chunk.Length.
        var chunkLength = (int)Math.Min(length, (ulong)MemsetChunkSize);
        var chunk = value == 0 ? _zeroChunk : ArrayPool<byte>.Shared.Rent(chunkLength);
        if (value != 0)
        {
            chunk.AsSpan(0, chunkLength).Fill(value);
        }

        try
        {
            var remaining = length;
            var cursor = destination;
            while (remaining > 0)
            {
                var take = (int)Math.Min((ulong)chunkLength, remaining);
                if (!TryWriteCompat(ctx, cursor, chunk.AsSpan(0, take)))
                {
                    // Clamp oversized clears to the valid mapped prefix. Small
                    // inaccessible writes are tolerated for compatibility with
                    // titles that probe optional state during startup.
                    if (length <= 0x40)
                    {
                        var recoveryIndex = Interlocked.Increment(ref _inaccessibleMemsetRecoveryCount);
                        if (recoveryIndex <= 8)
                        {
                            Log.Warn($"memset inaccessible-dst recovery#{recoveryIndex}: rip=0x{ctx.Rip:X16} dst=0x{destination:X16} len=0x{length:X} val=0x{value:X2}");
                        }

                        ctx[CpuRegister.Rax] = destination;
                        return (int)OrbisGen2Result.ORBIS_GEN2_OK;
                    }

                    var clampIndex = Interlocked.Increment(ref _inaccessibleMemsetRecoveryCount);
                    if (clampIndex <= 8)
                    {
                        Console.Error.WriteLine(
                            $"[LOADER][WARNING] memset clamped to mapped range#{clampIndex}: rip=0x{ctx.Rip:X16} " +
                            $"dst=0x{destination:X16} len=0x{length:X} written=0x{cursor - destination:X} val=0x{value:X2}");
                    }

                    ctx[CpuRegister.Rax] = destination;
                    return (int)OrbisGen2Result.ORBIS_GEN2_OK;
                }

                cursor += (ulong)take;
                remaining -= (ulong)take;
            }
        }
        finally
        {
            if (value != 0)
            {
                ArrayPool<byte>.Shared.Return(chunk);
            }
        }

        ctx[CpuRegister.Rax] = destination;
        return (int)OrbisGen2Result.ORBIS_GEN2_OK;
    }

    [SysAbiExport(
        Nid = "j4ViWNHEgww",
        ExportName = "strlen",
        Target = Generation.Gen4 | Generation.Gen5,
        LibraryName = "libc")]
    public static int Strlen(CpuContext ctx)
    {
        if (!TryReadCString(ctx, ctx[CpuRegister.Rdi], 1_048_576, out var bytes))
        {
            return (int)OrbisGen2Result.ORBIS_GEN2_ERROR_MEMORY_FAULT;
        }

        ctx[CpuRegister.Rax] = unchecked((ulong)bytes.Length);
        return (int)OrbisGen2Result.ORBIS_GEN2_OK;
    }

    [SysAbiExport(
        Nid = "5jNubw4vlAA",
        ExportName = "strnlen",
        Target = Generation.Gen4 | Generation.Gen5,
        LibraryName = "libc")]
    public static int Strnlen(CpuContext ctx)
    {
        var maxLength = ctx[CpuRegister.Rsi];
        if (!TryReadCString(ctx, ctx[CpuRegister.Rdi], maxLength, out var bytes))
        {
            return (int)OrbisGen2Result.ORBIS_GEN2_ERROR_MEMORY_FAULT;
        }

        ctx[CpuRegister.Rax] = unchecked((ulong)bytes.Length);
        return (int)OrbisGen2Result.ORBIS_GEN2_OK;
    }

    [SysAbiExport(
        Nid = "LHMrG7e8G78",
        ExportName = "wcsmisc",
        Target = Generation.Gen4 | Generation.Gen5,
        LibraryName = "libc")]
    public static int Wcslen(CpuContext ctx)
    {
        return WcslenCore(ctx, ctx[CpuRegister.Rdi]);
    }

    [SysAbiExport(
        Nid = "WkkeywLJcgU",
        ExportName = "wcslen",
        Target = Generation.Gen4 | Generation.Gen5,
        LibraryName = "libc")]
    public static int WcslenWkkey(CpuContext ctx)
    {
        return WcslenCore(ctx, ctx[CpuRegister.Rdi]);
    }

    private static int WcslenCore(CpuContext ctx, ulong address)
    {
        if (string.Equals(Environment.GetEnvironmentVariable("SHARPEMU_LOG_WIDE"), "1", StringComparison.Ordinal))
        {
            Span<byte> probe = stackalloc byte[32];
            if (TryReadCompat(ctx, address, probe))
            {
                Log.Trace($"wcslen probe @0x{address:X16}: {Convert.ToHexString(probe).ToLowerInvariant()}");
            }
            else
            {
                Log.Trace($"wcslen probe @0x{address:X16}: <unreadable>");
            }
        }

        if (!TryReadWideCString(ctx, address, 1_048_576, out var units))
        {
            Log.Warn($"wcslen: unreadable string at 0x{address:X16}");
            return (int)OrbisGen2Result.ORBIS_GEN2_ERROR_MEMORY_FAULT;
        }

        ctx[CpuRegister.Rax] = unchecked((ulong)units.Length);
        return (int)OrbisGen2Result.ORBIS_GEN2_OK;
    }

    [SysAbiExport(
        Nid = "Ovb2dSJOAuE",
        ExportName = "strcmp",
        Target = Generation.Gen4 | Generation.Gen5,
        LibraryName = "libc")]
    public static int Strcmp(CpuContext ctx)
    {
        var left = ctx[CpuRegister.Rdi];
        var right = ctx[CpuRegister.Rsi];
        if (!TryCompareStrings(ctx, left, right, limit: ulong.MaxValue, out var compare))
        {
            return (int)OrbisGen2Result.ORBIS_GEN2_ERROR_MEMORY_FAULT;
        }

        ctx[CpuRegister.Rax] = unchecked((ulong)compare);
        return (int)OrbisGen2Result.ORBIS_GEN2_OK;
    }

    [SysAbiExport(
        Nid = "fV2xHER+bKE",
        ExportName = "wcscoll",
        Target = Generation.Gen4 | Generation.Gen5,
        LibraryName = "libc")]
    public static int Wcscoll(CpuContext ctx)
    {
        return WcscollCore(ctx, ctx[CpuRegister.Rdi], ctx[CpuRegister.Rsi]);
    }

    [SysAbiExport(
        Nid = "pNtJdE3x49E",
        ExportName = "wcscmp",
        Target = Generation.Gen4 | Generation.Gen5,
        LibraryName = "libc")]
    public static int Wcscmp(CpuContext ctx)
    {
        return WcscmpCore(ctx, ctx[CpuRegister.Rdi], ctx[CpuRegister.Rsi]);
    }

    private static int WcscollCore(CpuContext ctx, ulong left, ulong right)
    {
        return WcscmpCore(ctx, left, right);
    }

    private static int WcscmpCore(CpuContext ctx, ulong left, ulong right)
    {
        if (!TryCompareWideStrings(ctx, left, right, limit: ulong.MaxValue, out var compare))
        {
            return (int)OrbisGen2Result.ORBIS_GEN2_ERROR_MEMORY_FAULT;
        }

        ctx[CpuRegister.Rax] = unchecked((ulong)compare);
        return (int)OrbisGen2Result.ORBIS_GEN2_OK;
    }

    [SysAbiExport(
        Nid = "FM5NPnLqBc8",
        ExportName = "wcscpy",
        Target = Generation.Gen4 | Generation.Gen5,
        LibraryName = "libc")]
    public static int WcscpyFm5(CpuContext ctx)
    {
        return WcscpyCore(ctx, ctx[CpuRegister.Rdi], ctx[CpuRegister.Rsi]);
    }

    private static int WcscpyCore(CpuContext ctx, ulong destination, ulong source)
    {
        if (source == 0)
        {
            var recoveryIndex = Interlocked.Increment(ref _nullWcscpyRecoveryCount);
            if (recoveryIndex <= 8)
            {
                Log.Warn($"wcscpy null-src recovery#{recoveryIndex}: rip=0x{ctx.Rip:X16} dst=0x{destination:X16}");
            }

            if (!TryWriteWideTerminator(ctx, destination))
            {
                return (int)OrbisGen2Result.ORBIS_GEN2_ERROR_MEMORY_FAULT;
            }

            ctx[CpuRegister.Rax] = destination;
            return (int)OrbisGen2Result.ORBIS_GEN2_OK;
        }

        if (!TryReadWideCString(ctx, source, 1_048_576, out var units))
        {
            return (int)OrbisGen2Result.ORBIS_GEN2_ERROR_MEMORY_FAULT;
        }

        if (!TryWriteCompat(ctx, destination, EncodeWideUnitsWithTerminator(units)))
        {
            return (int)OrbisGen2Result.ORBIS_GEN2_ERROR_MEMORY_FAULT;
        }

        ctx[CpuRegister.Rax] = destination;
        return (int)OrbisGen2Result.ORBIS_GEN2_OK;
    }

    [SysAbiExport(
        Nid = "aesyjrHVWy4",
        ExportName = "strncmp",
        Target = Generation.Gen4 | Generation.Gen5,
        LibraryName = "libc")]
    public static int Strncmp(CpuContext ctx)
    {
        var left = ctx[CpuRegister.Rdi];
        var right = ctx[CpuRegister.Rsi];
        var limit = ctx[CpuRegister.Rdx];
        if (!TryCompareStrings(ctx, left, right, limit, out var compare))
        {
            return (int)OrbisGen2Result.ORBIS_GEN2_ERROR_MEMORY_FAULT;
        }

        ctx[CpuRegister.Rax] = unchecked((ulong)compare);
        return (int)OrbisGen2Result.ORBIS_GEN2_OK;
    }

    [SysAbiExport(
        Nid = "AV6ipCNa4Rw",
        ExportName = "strcasecmp",
        Target = Generation.Gen4 | Generation.Gen5,
        LibraryName = "libc")]
    public static int Strcasecmp(CpuContext ctx)
    {
        var left = ctx[CpuRegister.Rdi];
        var right = ctx[CpuRegister.Rsi];
        if (left == 0 || right == 0)
        {
            var recoveryIndex = Interlocked.Increment(ref _nullStrcasecmpRecoveryCount);
            if (recoveryIndex <= 16)
            {
                var otherAddress = left == 0 ? right : left;
                var otherText = otherAddress != 0 && TryReadNullTerminatedUtf8(ctx, otherAddress, 256, out var text)
                    ? text
                    : "<unreadable>";
                _ = ctx.TryReadUInt64(ctx[CpuRegister.Rsp], out var returnRip);
                Log.Warn($"strcasecmp null-arg recovery#{recoveryIndex}: ret=0x{returnRip:X16} left=0x{left:X16} right=0x{right:X16} other=\"{otherText}\"");
            }

            // Real strcasecmp(NULL, x) is undefined behaviour and previously crashed inside the
            // LLE-routed implementation. Treat it as "not equal" instead so callers doing
            // `if (strcasecmp(a, b) == 0)` degrade gracefully rather than taking down the guest.
            ctx[CpuRegister.Rax] = left == right ? 0uL : 1uL;
            return (int)OrbisGen2Result.ORBIS_GEN2_OK;
        }

        if (!TryCompareStringsCaseInsensitive(ctx, left, right, limit: ulong.MaxValue, out var compare))
        {
            ctx[CpuRegister.Rax] = 1;
            return (int)OrbisGen2Result.ORBIS_GEN2_ERROR_MEMORY_FAULT;
        }

        ctx[CpuRegister.Rax] = unchecked((ulong)compare);
        return (int)OrbisGen2Result.ORBIS_GEN2_OK;
    }

    private static bool TryCompareStringsCaseInsensitive(CpuContext ctx, ulong left, ulong right, ulong limit, out int compare)
    {
        compare = 0;
        if (left == 0 || right == 0)
        {
            return false;
        }

        var max = limit == ulong.MaxValue ? 1_048_576UL : Math.Min(limit, 1_048_576UL);
        Span<byte> leftByte = stackalloc byte[1];
        Span<byte> rightByte = stackalloc byte[1];
        for (ulong i = 0; i < max; i++)
        {
            if (!TryReadCompat(ctx, left + i, leftByte) ||
                !TryReadCompat(ctx, right + i, rightByte))
            {
                return false;
            }

            var leftLower = ToAsciiLower(leftByte[0]);
            var rightLower = ToAsciiLower(rightByte[0]);
            compare = leftLower - rightLower;
            if (compare != 0 || leftByte[0] == 0 || rightByte[0] == 0)
            {
                return true;
            }
        }

        compare = 0;
        return true;
    }

    private static byte ToAsciiLower(byte value) => value is >= (byte)'A' and <= (byte)'Z' ? (byte)(value + 32) : value;

    [SysAbiExport(
        Nid = "0nV21JjYCH8",
        ExportName = "wcsncpy",
        Target = Generation.Gen4 | Generation.Gen5,
        LibraryName = "libc")]
    public static int Wcsncpy(CpuContext ctx)
    {
        return WcsncpyCore(ctx, ctx[CpuRegister.Rdi], ctx[CpuRegister.Rsi], ctx[CpuRegister.Rdx]);
    }

    [SysAbiExport(
        Nid = "E8wCoUEbfzk",
        ExportName = "wcsncmp",
        Target = Generation.Gen4 | Generation.Gen5,
        LibraryName = "libc")]
    public static int Wcsncmp(CpuContext ctx)
    {
        return WcsncmpCore(ctx, ctx[CpuRegister.Rdi], ctx[CpuRegister.Rsi], ctx[CpuRegister.Rdx]);
    }

    private static int WcsncmpCore(CpuContext ctx, ulong left, ulong right, ulong limit)
    {
        if (!TryCompareWideStrings(ctx, left, right, limit, out var compare))
        {
            return (int)OrbisGen2Result.ORBIS_GEN2_ERROR_MEMORY_FAULT;
        }

        ctx[CpuRegister.Rax] = unchecked((ulong)compare);
        return (int)OrbisGen2Result.ORBIS_GEN2_OK;
    }

    [SysAbiExport(
        Nid = "eLdDw6l0-bU",
        ExportName = "snprintf",
        Target = Generation.Gen4 | Generation.Gen5,
        LibraryName = "libc")]
    public static int Snprintf(CpuContext ctx)
    {
        return SnprintfCore(ctx);
    }

    [SysAbiExport(
        Nid = "Q2V+iqvjgC0",
        ExportName = "vsnprintf",
        Target = Generation.Gen4 | Generation.Gen5,
        LibraryName = "libc")]
    public static int Vsnprintf(CpuContext ctx)
    {
        return VsnprintfCore(ctx);
    }

    [SysAbiExport(
        Nid = "nJz16JE1txM",
        ExportName = "swprintf",
        Target = Generation.Gen4 | Generation.Gen5,
        LibraryName = "libc")]
    public static int Swprintf(CpuContext ctx)
    {
        return SwprintfCore(ctx);
    }

    [SysAbiExport(
        Nid = "u0XOsuOmOzc",
        ExportName = "vswprintf",
        Target = Generation.Gen4 | Generation.Gen5,
        LibraryName = "libc")]
    public static int Vswprintf(CpuContext ctx)
    {
        return VswprintfCore(ctx);
    }

    [SysAbiExport(
        Nid = "Im55VJ-Bekc",
        ExportName = "swprintf_s",
        Target = Generation.Gen4 | Generation.Gen5,
        LibraryName = "libc")]
    public static int SwprintfS(CpuContext ctx)
    {
        return SwprintfCore(ctx);
    }

    [SysAbiExport(
        Nid = "oDoV9tyHTbA",
        ExportName = "vswprintf_s",
        Target = Generation.Gen4 | Generation.Gen5,
        LibraryName = "libc")]
    public static int VswprintfS(CpuContext ctx)
    {
        return VswprintfCore(ctx);
    }

    [SysAbiExport(
        Nid = "GMpvxPFW924",
        ExportName = "vprintf",
        Target = Generation.Gen4 | Generation.Gen5,
        LibraryName = "libc")]
    public static int Vprintf(CpuContext ctx)
    {
        var formatAddress = ctx[CpuRegister.Rdi];
        var vaListAddress = ctx[CpuRegister.Rsi];
        if (!TryReadCString(ctx, formatAddress, 1_048_576, out var formatBytes))
        {
            return (int)OrbisGen2Result.ORBIS_GEN2_ERROR_MEMORY_FAULT;
        }

        var format = Encoding.UTF8.GetString(formatBytes);
        string rendered;
        if (!TryCreateVaListCursor(ctx, vaListAddress, out var vaCursor))
        {
            rendered = format;
        }
        else
        {
            rendered = FormatString(ctx, format, ref vaCursor);
        }

        Console.Write(rendered);
        ctx[CpuRegister.Rax] = unchecked((ulong)Encoding.UTF8.GetByteCount(rendered));
        return (int)OrbisGen2Result.ORBIS_GEN2_OK;
    }

    [SysAbiExport(
        Nid = "kiZSXIWd9vg",
        ExportName = "strcpy",
        Target = Generation.Gen4 | Generation.Gen5,
        LibraryName = "libc")]
    public static int Strcpy(CpuContext ctx)
    {
        var destination = ctx[CpuRegister.Rdi];
        var source = ctx[CpuRegister.Rsi];
        if (!TryReadCString(ctx, source, 1_048_576, out var bytes))
        {
            return (int)OrbisGen2Result.ORBIS_GEN2_ERROR_MEMORY_FAULT;
        }

        var payload = new byte[bytes.Length + 1];
        bytes.CopyTo(payload.AsSpan());
        if (!TryWriteCompat(ctx, destination, payload))
        {
            return (int)OrbisGen2Result.ORBIS_GEN2_ERROR_MEMORY_FAULT;
        }

        ctx[CpuRegister.Rax] = destination;
        return (int)OrbisGen2Result.ORBIS_GEN2_OK;
    }

    [SysAbiExport(
        Nid = "6f5f-qx4ucA",
        ExportName = "wcscpy_s",
        Target = Generation.Gen4 | Generation.Gen5,
        LibraryName = "libc")]
    public static int WcscpyS(CpuContext ctx)
    {
        return WcscpySCore(ctx, ctx[CpuRegister.Rdi], ctx[CpuRegister.Rsi], ctx[CpuRegister.Rdx]);
    }

    [SysAbiExport(
        Nid = "6sJWiWSRuqk",
        ExportName = "strncpy",
        Target = Generation.Gen4 | Generation.Gen5,
        LibraryName = "libc")]
    public static int Strncpy(CpuContext ctx)
    {
        var destination = ctx[CpuRegister.Rdi];
        var source = ctx[CpuRegister.Rsi];
        var count = (int)Math.Min(ctx[CpuRegister.Rdx], int.MaxValue);
        if (count < 0)
        {
            return (int)OrbisGen2Result.ORBIS_GEN2_ERROR_INVALID_ARGUMENT;
        }

        var payload = new byte[count];
        Span<byte> one = stackalloc byte[1];
        var copied = 0;
        while (copied < count)
        {
            if (!TryReadCompat(ctx, source + (ulong)copied, one))
            {
                return (int)OrbisGen2Result.ORBIS_GEN2_ERROR_MEMORY_FAULT;
            }

            payload[copied] = one[0];
            copied++;
            if (one[0] == 0)
            {
                break;
            }
        }

        if (!TryWriteCompat(ctx, destination, payload))
        {
            return (int)OrbisGen2Result.ORBIS_GEN2_ERROR_MEMORY_FAULT;
        }

        ctx[CpuRegister.Rax] = destination;
        return (int)OrbisGen2Result.ORBIS_GEN2_OK;
    }

    [SysAbiExport(
        Nid = "Slmz4HMpNGs",
        ExportName = "wcsncpy_s",
        Target = Generation.Gen4 | Generation.Gen5,
        LibraryName = "libc")]
    public static int WcsncpyS(CpuContext ctx)
    {
        return WcsncpySCore(ctx, ctx[CpuRegister.Rdi], ctx[CpuRegister.Rsi], ctx[CpuRegister.Rdx], ctx[CpuRegister.Rcx]);
    }

    private static int WcsncpyCore(CpuContext ctx, ulong destination, ulong source, ulong countValue)
    {
        var count = (int)Math.Min(countValue, int.MaxValue);
        if (count < 0 || count > (int.MaxValue / WideCharSize))
        {
            return (int)OrbisGen2Result.ORBIS_GEN2_ERROR_INVALID_ARGUMENT;
        }

        var payload = new byte[count * WideCharSize];
        if (count == 0)
        {
            ctx[CpuRegister.Rax] = destination;
            return (int)OrbisGen2Result.ORBIS_GEN2_OK;
        }

        // Keep host-pointer reads page-bounded and copy several UTF-16 code
        // units per validation. Large scratch strings otherwise pay the host
        // address-validation and temporary-buffer cost once per character.
        const int maxReadBytes = 4096;
        var readBuffer = GC.AllocateUninitializedArray<byte>(
            Math.Min(maxReadBytes, payload.Length));
        var copied = 0;
        while (copied < count)
        {
            var sourceAddress = source + ((ulong)copied * WideCharSize);
            if (sourceAddress < source)
            {
                return (int)OrbisGen2Result.ORBIS_GEN2_ERROR_MEMORY_FAULT;
            }

            var pageBytesRemaining = maxReadBytes -
                (int)(sourceAddress & (maxReadBytes - 1));
            var remainingBytes = (count - copied) * WideCharSize;
            var readBytes = Math.Min(
                readBuffer.Length,
                Math.Min(pageBytesRemaining, remainingBytes));
            readBytes &= ~(WideCharSize - 1);
            if (readBytes == 0 ||
                !TryReadCompat(ctx, sourceAddress, readBuffer.AsSpan(0, readBytes)))
            {
                return (int)OrbisGen2Result.ORBIS_GEN2_ERROR_MEMORY_FAULT;
            }

            for (var offset = 0; offset < readBytes; offset += WideCharSize)
            {
                var unit = BinaryPrimitives.ReadUInt16LittleEndian(
                    readBuffer.AsSpan(offset, WideCharSize));
                if (unit == 0)
                {
                    // payload is zero-initialized, supplying wcsncpy padding.
                    copied = count;
                    break;
                }

                BinaryPrimitives.WriteUInt16LittleEndian(
                    payload.AsSpan((copied * WideCharSize) + offset, WideCharSize),
                    unit);
            }

            if (copied != count)
            {
                copied += readBytes / WideCharSize;
            }
        }

        if (!TryWriteCompat(ctx, destination, payload))
        {
            return (int)OrbisGen2Result.ORBIS_GEN2_ERROR_MEMORY_FAULT;
        }

        ctx[CpuRegister.Rax] = destination;
        return (int)OrbisGen2Result.ORBIS_GEN2_OK;
    }

    [SysAbiExport(
        Nid = "Ezzq78ZgHPs",
        ExportName = "wcschr",
        Target = Generation.Gen4 | Generation.Gen5,
        LibraryName = "libc")]
    public static int Wcschr(CpuContext ctx)
    {
        return WcschrCore(ctx, ctx[CpuRegister.Rdi], unchecked((ushort)ctx[CpuRegister.Rsi]));
    }

    private static int WcschrCore(CpuContext ctx, ulong address, ushort needle)
    {
        const int maxReadBytes = 4096;
        var readBuffer = GC.AllocateUninitializedArray<byte>(maxReadBytes);
        const ulong maxUnits = 1_048_576;
        for (ulong index = 0; index < maxUnits;)
        {
            var unitAddress = address + (index * WideCharSize);
            if (unitAddress < address)
            {
                return (int)OrbisGen2Result.ORBIS_GEN2_ERROR_MEMORY_FAULT;
            }

            var remainingBytes = (maxUnits - index) * WideCharSize;
            var pageBytesRemaining = maxReadBytes -
                (int)(unitAddress & (maxReadBytes - 1));
            var readBytes = (int)Math.Min(
                (ulong)Math.Min(readBuffer.Length, pageBytesRemaining),
                remainingBytes);
            readBytes &= ~(WideCharSize - 1);
            if (readBytes == 0 ||
                !TryReadCompat(ctx, unitAddress, readBuffer.AsSpan(0, readBytes)))
            {
                return (int)OrbisGen2Result.ORBIS_GEN2_ERROR_MEMORY_FAULT;
            }

            for (var offset = 0; offset < readBytes; offset += WideCharSize)
            {
                var unit = BinaryPrimitives.ReadUInt16LittleEndian(
                    readBuffer.AsSpan(offset, WideCharSize));
                if (unit == needle)
                {
                    ctx[CpuRegister.Rax] = unitAddress + (ulong)offset;
                    return (int)OrbisGen2Result.ORBIS_GEN2_OK;
                }

                if (unit == 0)
                {
                    ctx[CpuRegister.Rax] = 0;
                    return (int)OrbisGen2Result.ORBIS_GEN2_OK;
                }
            }

            index += (ulong)(readBytes / WideCharSize);
        }

        ctx[CpuRegister.Rax] = 0;
        return (int)OrbisGen2Result.ORBIS_GEN2_OK;
    }

    private static int WcscpySCore(CpuContext ctx, ulong destination, ulong destinationCount, ulong source)
    {
        if (destination == 0 || destinationCount == 0)
        {
            ctx[CpuRegister.Rax] = Einval;
            return (int)OrbisGen2Result.ORBIS_GEN2_OK;
        }

        if (source == 0)
        {
            if (!TryZeroWideDestination(ctx, destination, destinationCount))
            {
                return (int)OrbisGen2Result.ORBIS_GEN2_ERROR_MEMORY_FAULT;
            }

            ctx[CpuRegister.Rax] = Einval;
            return (int)OrbisGen2Result.ORBIS_GEN2_OK;
        }

        var probeLimit = Math.Min(destinationCount, 1_048_576UL);
        if (!TryReadWideCStringBounded(ctx, source, probeLimit, out var units, out var terminated))
        {
            _ = TryZeroWideDestination(ctx, destination, destinationCount);
            return (int)OrbisGen2Result.ORBIS_GEN2_ERROR_MEMORY_FAULT;
        }

        if (!terminated || (ulong)units.Length + 1 > destinationCount)
        {
            if (!TryZeroWideDestination(ctx, destination, destinationCount))
            {
                return (int)OrbisGen2Result.ORBIS_GEN2_ERROR_MEMORY_FAULT;
            }

            ctx[CpuRegister.Rax] = Erange;
            return (int)OrbisGen2Result.ORBIS_GEN2_OK;
        }

        if (!TryWriteCompat(ctx, destination, EncodeWideUnitsWithTerminator(units)))
        {
            return (int)OrbisGen2Result.ORBIS_GEN2_ERROR_MEMORY_FAULT;
        }

        ctx[CpuRegister.Rax] = 0;
        return (int)OrbisGen2Result.ORBIS_GEN2_OK;
    }

    private static int WcsncpySCore(CpuContext ctx, ulong destination, ulong destinationCount, ulong source, ulong count)
    {
        if (destination == 0 || destinationCount == 0)
        {
            ctx[CpuRegister.Rax] = Einval;
            return (int)OrbisGen2Result.ORBIS_GEN2_OK;
        }

        if (source == 0)
        {
            if (!TryZeroWideDestination(ctx, destination, destinationCount))
            {
                return (int)OrbisGen2Result.ORBIS_GEN2_ERROR_MEMORY_FAULT;
            }

            ctx[CpuRegister.Rax] = Einval;
            return (int)OrbisGen2Result.ORBIS_GEN2_OK;
        }

        if (count == 0)
        {
            if (!TryWriteWideTerminator(ctx, destination))
            {
                return (int)OrbisGen2Result.ORBIS_GEN2_ERROR_MEMORY_FAULT;
            }

            ctx[CpuRegister.Rax] = 0;
            return (int)OrbisGen2Result.ORBIS_GEN2_OK;
        }

        if (count == ulong.MaxValue)
        {
            var copyLimit = Math.Min(destinationCount - 1, 1_048_576UL);
            if (!TryReadWideCStringBounded(ctx, source, copyLimit, out var truncatedUnits, out var terminated))
            {
                _ = TryZeroWideDestination(ctx, destination, destinationCount);
                return (int)OrbisGen2Result.ORBIS_GEN2_ERROR_MEMORY_FAULT;
            }

            if (!TryWriteCompat(ctx, destination, EncodeWideUnitsWithTerminator(truncatedUnits)))
            {
                return (int)OrbisGen2Result.ORBIS_GEN2_ERROR_MEMORY_FAULT;
            }

            ctx[CpuRegister.Rax] = terminated ? 0UL : Struncate;
            return (int)OrbisGen2Result.ORBIS_GEN2_OK;
        }

        var boundedCount = Math.Min(count, 1_048_576UL);
        if (!TryReadWideCStringBounded(ctx, source, boundedCount, out var units, out var sourceTerminated))
        {
            _ = TryZeroWideDestination(ctx, destination, destinationCount);
            return (int)OrbisGen2Result.ORBIS_GEN2_ERROR_MEMORY_FAULT;
        }

        var requiredUnits = sourceTerminated ? (ulong)units.Length + 1 : boundedCount + 1;
        if (requiredUnits > destinationCount)
        {
            if (!TryZeroWideDestination(ctx, destination, destinationCount))
            {
                return (int)OrbisGen2Result.ORBIS_GEN2_ERROR_MEMORY_FAULT;
            }

            ctx[CpuRegister.Rax] = Erange;
            return (int)OrbisGen2Result.ORBIS_GEN2_OK;
        }

        if (!TryWriteCompat(ctx, destination, EncodeWideUnitsWithTerminator(units)))
        {
            return (int)OrbisGen2Result.ORBIS_GEN2_ERROR_MEMORY_FAULT;
        }

        ctx[CpuRegister.Rax] = 0;
        return (int)OrbisGen2Result.ORBIS_GEN2_OK;
    }

    [SysAbiExport(
        Nid = "Q3VBxCXhUHs",
        ExportName = "memcpy",
        Target = Generation.Gen4 | Generation.Gen5,
        LibraryName = "libc")]
    public static int Memcpy(CpuContext ctx)
    {
        var destination = ctx[CpuRegister.Rdi];
        var source = ctx[CpuRegister.Rsi];
        var rawCount = ctx[CpuRegister.Rdx];
        var count = (int)Math.Min(rawCount, int.MaxValue);
        if (count < 0)
        {
            Log.Warn($"memcpy oversized count rejected: dst=0x{destination:X16} src=0x{source:X16} count=0x{rawCount:X}");
            ctx[CpuRegister.Rax] = destination;
            return (int)OrbisGen2Result.ORBIS_GEN2_ERROR_INVALID_ARGUMENT;
        }

        var payload = GC.AllocateUninitializedArray<byte>(count);
        if (count > 0 && (!TryReadCompat(ctx, source, payload) || !TryWriteCompat(ctx, destination, payload)))
        {
            return (int)OrbisGen2Result.ORBIS_GEN2_ERROR_MEMORY_FAULT;
        }

        return (int)OrbisGen2Result.ORBIS_GEN2_OK;
    }

    [SysAbiExport(
        Nid = "+P6FRGH4LfA",
        ExportName = "memmove",
        Target = Generation.Gen4 | Generation.Gen5,
        LibraryName = "libc")]
    public static int Memmove(CpuContext ctx)
    {
        return Memcpy(ctx);
    }

    [SysAbiExport(
        Nid = "gQX+4GDQjpM",
        ExportName = "malloc",
        Target = Generation.Gen4 | Generation.Gen5,
        LibraryName = "libc")]
    public static int Malloc(CpuContext ctx)
    {
        ctx[CpuRegister.Rax] =
            TryAllocateLibcHeap(ctx[CpuRegister.Rdi], DefaultLibcHeapAlignment, zeroFill: false, out var address)
                ? address
                : 0;
        TraceLibcAllocation(
            ctx,
            "malloc",
            size: ctx[CpuRegister.Rdi],
            alignment: DefaultLibcHeapAlignment,
            resultAddress: ctx[CpuRegister.Rax]);
        return (int)OrbisGen2Result.ORBIS_GEN2_OK;
    }

    [SysAbiExport(
        Nid = "tIhsqj0qsFE",
        ExportName = "free",
        Target = Generation.Gen4 | Generation.Gen5,
        LibraryName = "libc")]
    public static int Free(CpuContext ctx)
    {
        FreeLibcHeap(ctx[CpuRegister.Rdi]);
        ctx[CpuRegister.Rax] = 0;
        return (int)OrbisGen2Result.ORBIS_GEN2_OK;
    }

    [SysAbiExport(
        Nid = "2X5agFjKxMc",
        ExportName = "calloc",
        Target = Generation.Gen4 | Generation.Gen5,
        LibraryName = "libc")]
    public static int Calloc(CpuContext ctx)
    {
        ctx[CpuRegister.Rax] =
            TryMultiplyAllocationSize(ctx[CpuRegister.Rdi], ctx[CpuRegister.Rsi], out var totalSize) &&
            TryAllocateLibcHeapCore(totalSize, DefaultLibcHeapAlignment, zeroFill: true, out var address)
                ? address
                : 0;
        TraceLibcAllocation(
            ctx,
            "calloc",
            size: ctx[CpuRegister.Rdi],
            count: ctx[CpuRegister.Rsi],
            alignment: DefaultLibcHeapAlignment,
            resultAddress: ctx[CpuRegister.Rax]);
        return (int)OrbisGen2Result.ORBIS_GEN2_OK;
    }

    [SysAbiExport(
        Nid = "Y7aJ1uydPMo",
        ExportName = "realloc",
        Target = Generation.Gen4 | Generation.Gen5,
        LibraryName = "libc")]
    public static int Realloc(CpuContext ctx)
    {
        var existingAddress = ctx[CpuRegister.Rdi];
        var requestedSize = ctx[CpuRegister.Rsi];

        if (existingAddress == 0)
        {
            ctx[CpuRegister.Rax] =
                TryAllocateLibcHeap(requestedSize, DefaultLibcHeapAlignment, zeroFill: false, out var freshAddress)
                    ? freshAddress
                    : 0;
            return (int)OrbisGen2Result.ORBIS_GEN2_OK;
        }

        if (requestedSize == 0)
        {
            FreeLibcHeap(existingAddress);
            ctx[CpuRegister.Rax] = 0;
            return (int)OrbisGen2Result.ORBIS_GEN2_OK;
        }

        ctx[CpuRegister.Rax] =
            TryReallocateLibcHeap(existingAddress, requestedSize, out var resizedAddress)
                ? resizedAddress
                : 0;
        TraceLibcAllocation(
            ctx,
            "realloc",
            size: requestedSize,
            existingAddress: existingAddress,
            resultAddress: ctx[CpuRegister.Rax]);
        return (int)OrbisGen2Result.ORBIS_GEN2_OK;
    }

    [SysAbiExport(
        Nid = "Ujf3KzMvRmI",
        ExportName = "memalign",
        Target = Generation.Gen4 | Generation.Gen5,
        LibraryName = "libc")]
    public static int Memalign(CpuContext ctx)
    {
        ctx[CpuRegister.Rax] =
            TryAllocateAlignedLibcHeap(
                alignmentValue: ctx[CpuRegister.Rdi],
                requestedSize: ctx[CpuRegister.Rsi],
                requireSizeMultiple: false,
                out var address)
                ? address
                : 0;
        TraceLibcAllocation(
            ctx,
            "memalign",
            size: ctx[CpuRegister.Rsi],
            alignment: ctx[CpuRegister.Rdi],
            resultAddress: ctx[CpuRegister.Rax]);
        return (int)OrbisGen2Result.ORBIS_GEN2_OK;
    }

    [SysAbiExport(
        Nid = "2Btkg8k24Zg",
        ExportName = "aligned_alloc",
        Target = Generation.Gen4 | Generation.Gen5,
        LibraryName = "libc")]
    public static int AlignedAlloc(CpuContext ctx)
    {
        ctx[CpuRegister.Rax] =
            TryAllocateAlignedLibcHeap(
                alignmentValue: ctx[CpuRegister.Rdi],
                requestedSize: ctx[CpuRegister.Rsi],
                requireSizeMultiple: true,
                out var address)
                ? address
                : 0;
        TraceLibcAllocation(
            ctx,
            "aligned_alloc",
            size: ctx[CpuRegister.Rsi],
            alignment: ctx[CpuRegister.Rdi],
            resultAddress: ctx[CpuRegister.Rax]);
        return (int)OrbisGen2Result.ORBIS_GEN2_OK;
    }

    [SysAbiExport(
        Nid = "cVSk9y8URbc",
        ExportName = "posix_memalign",
        Target = Generation.Gen4 | Generation.Gen5,
        LibraryName = "libc")]
    public static int PosixMemalign(CpuContext ctx)
    {
        var outPointerAddress = ctx[CpuRegister.Rdi];
        if (outPointerAddress == 0)
        {
            ctx[CpuRegister.Rax] = Einval;
            TraceLibcAllocation(
                ctx,
                "posix_memalign",
                size: ctx[CpuRegister.Rdx],
                alignment: ctx[CpuRegister.Rsi],
                existingAddress: outPointerAddress,
                resultAddress: 0,
                errorCode: Einval);
            return (int)OrbisGen2Result.ORBIS_GEN2_OK;
        }

        if (!TryValidateAlignedAllocation(
                ctx[CpuRegister.Rsi],
                ctx[CpuRegister.Rdx],
                requireSizeMultiple: false,
                requirePointerSizedAlignment: true,
                out var alignment,
                out var requestedSize))
        {
            _ = TryWriteUInt64Compat(ctx, outPointerAddress, 0);
            ctx[CpuRegister.Rax] = Einval;
            TraceLibcAllocation(
                ctx,
                "posix_memalign",
                size: ctx[CpuRegister.Rdx],
                alignment: ctx[CpuRegister.Rsi],
                existingAddress: outPointerAddress,
                resultAddress: 0,
                errorCode: Einval);
            return (int)OrbisGen2Result.ORBIS_GEN2_OK;
        }

        if (!TryAllocateLibcHeapCore(requestedSize, alignment, zeroFill: false, out var address))
        {
            _ = TryWriteUInt64Compat(ctx, outPointerAddress, 0);
            ctx[CpuRegister.Rax] = Enomem;
            TraceLibcAllocation(
                ctx,
                "posix_memalign",
                size: requestedSize,
                alignment: alignment,
                existingAddress: outPointerAddress,
                resultAddress: 0,
                errorCode: Enomem);
            return (int)OrbisGen2Result.ORBIS_GEN2_OK;
        }

        if (!TryWriteUInt64Compat(ctx, outPointerAddress, address))
        {
            FreeLibcHeap(address);
            ctx[CpuRegister.Rax] = Einval;
            TraceLibcAllocation(
                ctx,
                "posix_memalign",
                size: requestedSize,
                alignment: alignment,
                existingAddress: outPointerAddress,
                resultAddress: 0,
                errorCode: Einval);
            return (int)OrbisGen2Result.ORBIS_GEN2_OK;
        }

        ctx[CpuRegister.Rax] = 0;
        TraceLibcAllocation(
            ctx,
            "posix_memalign",
            size: requestedSize,
            alignment: alignment,
            existingAddress: outPointerAddress,
            resultAddress: address);
        return (int)OrbisGen2Result.ORBIS_GEN2_OK;
    }

    // Was unresolved (returning the 0x80020002 sentinel, then crashing when the guest
    // dereferenced it) - the game's own heap instrumentation calls this hook when it
    // detects a corrupted/invalid block, not the emulator's allocator, so this is purely
    // a diagnostic sink: log what was reported and return success so the caller continues.
    [SysAbiExport(
        Nid = "al3JzFI9MQ0",
        ExportName = "sceLibcInternalHeapErrorReportForGame",
        Target = Generation.Gen4 | Generation.Gen5,
        LibraryName = "libSceLibcInternal")]
    public static int LibcInternalHeapErrorReportForGame(CpuContext ctx)
    {
        Log.Warn(
  $"sceLibcInternalHeapErrorReportForGame: rdi=0x{ctx[CpuRegister.Rdi]:X16} " +
            $"rsi=0x{ctx[CpuRegister.Rsi]:X16} rdx=0x{ctx[CpuRegister.Rdx]:X16} rcx=0x{ctx[CpuRegister.Rcx]:X16}"
);
        ctx[CpuRegister.Rax] = 0;
        return (int)OrbisGen2Result.ORBIS_GEN2_OK;
    }

    [SysAbiExport(
        Nid = "DfivPArhucg",
        ExportName = "memcmp",
        Target = Generation.Gen4 | Generation.Gen5,
        LibraryName = "libc")]
    public static int Memcmp(CpuContext ctx)
    {
        var left = ctx[CpuRegister.Rdi];
        var right = ctx[CpuRegister.Rsi];
        var count = (int)Math.Min(ctx[CpuRegister.Rdx], int.MaxValue);
        if (count < 0)
        {
            return (int)OrbisGen2Result.ORBIS_GEN2_ERROR_INVALID_ARGUMENT;
        }

        Span<byte> leftByte = stackalloc byte[1];
        Span<byte> rightByte = stackalloc byte[1];
        for (var i = 0; i < count; i++)
        {
            if (!TryReadCompat(ctx, left + (ulong)i, leftByte) ||
                !TryReadCompat(ctx, right + (ulong)i, rightByte))
            {
                return (int)OrbisGen2Result.ORBIS_GEN2_ERROR_MEMORY_FAULT;
            }

            var diff = leftByte[0] - rightByte[0];
            if (diff != 0)
            {
                ctx[CpuRegister.Rax] = unchecked((ulong)diff);
                return (int)OrbisGen2Result.ORBIS_GEN2_OK;
            }
        }

        ctx[CpuRegister.Rax] = 0;
        return (int)OrbisGen2Result.ORBIS_GEN2_OK;
    }

    [SysAbiExport(
        Nid = "QrZZdJ8XsX0",
        ExportName = "fputs",
        Target = Generation.Gen4 | Generation.Gen5,
        LibraryName = "libc")]
    public static int Fputs(CpuContext ctx)
    {
        var textAddress = ctx[CpuRegister.Rdi];
        var stream = ctx[CpuRegister.Rsi];
        if (textAddress == 0)
        {
            ctx[CpuRegister.Rax] = unchecked((ulong)(-1L));
            return (int)OrbisGen2Result.ORBIS_GEN2_ERROR_INVALID_ARGUMENT;
        }

        if (!TryReadNullTerminatedUtf8(ctx, textAddress, MaxGuestStringLength, out var text))
        {
            ctx[CpuRegister.Rax] = unchecked((ulong)(-1L));
            return (int)OrbisGen2Result.ORBIS_GEN2_ERROR_MEMORY_FAULT;
        }

        if (stream == 0)
        {
            Console.Error.Write(text);
            Console.Error.Flush();
        }
        else
        {
            Console.Out.Write(text);
            Console.Out.Flush();
        }

        ctx[CpuRegister.Rax] = unchecked((ulong)text.Length);
        return (int)OrbisGen2Result.ORBIS_GEN2_OK;
    }

    [SysAbiExport(
        Nid = "6c3rCVE-fTU",
        ExportName = "_open",
        Target = Generation.Gen4 | Generation.Gen5,
        LibraryName = "libKernel")]
    public static int KernelOpenUnderscore(CpuContext ctx)
    {
        var pathAddress = ctx[CpuRegister.Rdi];
        var flags = unchecked((int)ctx[CpuRegister.Rsi]);
        // Not migratable to [GuestCString]: the local reader's TryReadCompat host-memory
        // fallback recovers paths in loader-mapped regions that ctx.Memory cannot see.
        if (!TryReadNullTerminatedUtf8(ctx, pathAddress, MaxGuestStringLength, out var guestPath))
        {
            return (int)OrbisGen2Result.ORBIS_GEN2_ERROR_MEMORY_FAULT;
        }

        var hostPath = ResolveGuestPath(guestPath);
        var access = ResolveOpenAccess(flags);
        var mode = ResolveOpenMode(flags, access);
        try
        {
            if (Bink2MovieBridge.ShouldSkipGuestMovie(hostPath))
            {
                LogOpenTrace(
                    "_open bink-skip path='" + guestPath + "' host='" + hostPath +
                    "' flags=0x" + flags.ToString("X8"));
                Console.Error.WriteLine(
                    "[LOADER][INFO] Skipping Bink movie without a decoder: " +
                    Path.GetFileName(hostPath));
                return (int)OrbisGen2Result.ORBIS_GEN2_ERROR_NOT_FOUND;
            }

            if (IsMutatingOpen(flags) && IsReadOnlyGuestMutationPath(guestPath))
            {
                LogOpenTrace($"_open readonly path='{guestPath}' host='{hostPath}' flags=0x{flags:X8}");
                return (int)OrbisGen2Result.ORBIS_GEN2_ERROR_PERMISSION_DENIED;
            }

            var wantsDirectory = (flags & O_DIRECTORY) != 0;
            if (wantsDirectory || Directory.Exists(hostPath))
            {
                if (!Directory.Exists(hostPath))
                {
                    LogOpenTrace($"_open miss path='{guestPath}' host='{hostPath}' flags=0x{flags:X8} directory=1");
                    return (int)OrbisGen2Result.ORBIS_GEN2_ERROR_NOT_FOUND;
                }

                if (access != FileAccess.Read || (flags & (O_CREAT | O_TRUNC | O_APPEND)) != 0)
                {
                    LogOpenTrace($"_open invalid-dir path='{guestPath}' host='{hostPath}' flags=0x{flags:X8}");
                    return (int)OrbisGen2Result.ORBIS_GEN2_ERROR_INVALID_ARGUMENT;
                }

                var directoryFd = (int)Interlocked.Increment(ref _nextFileDescriptor);
                lock (_fdGate)
                {
                    _openDirectories[directoryFd] = new OpenDirectory
                    {
                        Path = hostPath,
                        Entries = EnumerateDirectoryEntries(hostPath),
                        NextIndex = 0
                    };
                }

                LogOpenTrace($"_open dir path='{guestPath}' host='{hostPath}' flags=0x{flags:X8} fd={directoryFd}");
                ctx[CpuRegister.Rax] = unchecked((ulong)directoryFd);
                return (int)OrbisGen2Result.ORBIS_GEN2_OK;
            }

            EnsureOpenParentDirectoryExists(guestPath, hostPath, flags);
            var stream = new FileStream(hostPath, mode, access, FileShare.ReadWrite);
            if ((flags & O_APPEND) != 0)
            {
                stream.Seek(0, SeekOrigin.End);
            }

            var fd = (int)Interlocked.Increment(ref _nextFileDescriptor);
            lock (_fdGate)
            {
                _openFiles[fd] = stream;
            }

            // Bink is linked directly into some games, so there is no media
            // import for the HLE codec layer to intercept. The successful
            // guest file open is the stable boundary at which the optional
            // host Bink bridge can attach to the same movie.
            Bink2MovieBridge.ObserveGuestMovie(hostPath);

            if (IsMutatingOpen(flags))
            {
                InvalidateNegativeStatCacheForPathAndAncestors(guestPath);
                InvalidateAprFileSizeCache(hostPath);
            }

            LogOpenTrace($"_open file path='{guestPath}' host='{hostPath}' flags=0x{flags:X8} fd={fd}");
            ctx[CpuRegister.Rax] = unchecked((ulong)fd);
            return (int)OrbisGen2Result.ORBIS_GEN2_OK;
        }
        catch (Exception ex) when (ex is IOException or UnauthorizedAccessException)
        {
            LogOpenTrace($"_open fail path='{guestPath}' host='{hostPath}' flags=0x{flags:X8} ex={ex.GetType().Name}: {ex.Message}");
            return ex is UnauthorizedAccessException
                ? (int)OrbisGen2Result.ORBIS_GEN2_ERROR_INVALID_ARGUMENT
                : (int)OrbisGen2Result.ORBIS_GEN2_ERROR_NOT_FOUND;
        }
    }

    [SysAbiExport(
        Nid = "NNtFaKJbPt0",
        ExportName = "_close",
        Target = Generation.Gen4 | Generation.Gen5,
        LibraryName = "libKernel")]
    public static int KernelCloseUnderscore(CpuContext ctx) => KernelCloseCore(ctx, unchecked((int)ctx[CpuRegister.Rdi]));

    [SysAbiExport(
        Nid = "bY-PO6JhzhQ",
        ExportName = "close",
        Target = Generation.Gen4 | Generation.Gen5,
        LibraryName = "libKernel")]
    public static int PosixClose(CpuContext ctx) => KernelCloseCore(ctx, unchecked((int)ctx[CpuRegister.Rdi]));

    [SysAbiExport(
        Nid = "UK2Tl2DWUns",
        ExportName = "sceKernelClose",
        Target = Generation.Gen4 | Generation.Gen5,
        LibraryName = "libKernel")]
    public static int KernelClose(CpuContext ctx) => KernelCloseCore(ctx, unchecked((int)ctx[CpuRegister.Rdi]));

    [SysAbiExport(
        Nid = "eV9wAD2riIA",
        ExportName = "sceKernelStat",
        Target = Generation.Gen4 | Generation.Gen5,
        LibraryName = "libKernel")]
    public static int KernelStat(CpuContext ctx)
    {
        var pathAddress = ctx[CpuRegister.Rdi];
        var statAddress = ctx[CpuRegister.Rsi];
        if (pathAddress == 0 || statAddress == 0)
        {
            return (int)OrbisGen2Result.ORBIS_GEN2_ERROR_INVALID_ARGUMENT;
        }

        if (!TryReadNullTerminatedUtf8(ctx, pathAddress, MaxGuestStringLength, out var guestPath))
        {
            return (int)OrbisGen2Result.ORBIS_GEN2_ERROR_MEMORY_FAULT;
        }

        var hostPath = ResolveGuestPath(guestPath);
        var statCacheKey = GetNegativeStatCacheKey(guestPath);
        if (statCacheKey is not null && IsNegativeStatCached(statCacheKey))
        {
            LogUniqueStatTrace(guestPath, hostPath, found: false);
            return (int)OrbisGen2Result.ORBIS_GEN2_ERROR_NOT_FOUND;
        }

        if (!TryWriteHostPathStat(ctx, statAddress, hostPath))
        {
            if (statCacheKey is not null)
            {
                AddNegativeStatCache(statCacheKey);
            }

            LogUniqueStatTrace(guestPath, hostPath, found: false);
            return (int)OrbisGen2Result.ORBIS_GEN2_ERROR_NOT_FOUND;
        }

        if (statCacheKey is not null)
        {
            RemoveNegativeStatCache(statCacheKey);
        }

        LogUniqueStatTrace(guestPath, hostPath, found: true);
        ctx[CpuRegister.Rax] = 0;
        return (int)OrbisGen2Result.ORBIS_GEN2_OK;
    }

    [SysAbiExport(
        Nid = "E6ao34wPw+U",
        ExportName = "stat",
        Target = Generation.Gen4 | Generation.Gen5,
        LibraryName = "libc")]
    public static int PosixStat(CpuContext ctx)
    {
        var result = KernelStat(ctx);
        if (result == (int)OrbisGen2Result.ORBIS_GEN2_OK)
        {
            return 0;
        }

        // stat(2) follows the libc/POSIX ABI: failures return -1 and expose
        // the reason through errno. Returning the raw Orbis kernel code here
        // makes callers treat a missing file as a non-negative success value.
        var errno = result switch
        {
            (int)OrbisGen2Result.ORBIS_GEN2_ERROR_INVALID_ARGUMENT => Einval,
            (int)OrbisGen2Result.ORBIS_GEN2_ERROR_MEMORY_FAULT => Efault,
            _ => 2, // ENOENT
        };
        KernelRuntimeCompatExports.TrySetErrno(ctx, errno);
        ctx[CpuRegister.Rax] = ulong.MaxValue;
        return -1;
    }

    [SysAbiExport(
        Nid = "gEpBkcwxUjw",
        ExportName = "sceKernelAprResolveFilepathsToIdsAndFileSizes",
        Target = Generation.Gen4 | Generation.Gen5,
        LibraryName = "libKernel")]
    public static int KernelAprResolveFilepathsToIdsAndFileSizes(CpuContext ctx)
    {
        var pathListAddress = ctx[CpuRegister.Rdi];
        var count = ctx[CpuRegister.Rsi];
        var idsAddress = ctx[CpuRegister.Rdx];
        var sizesAddress = ctx[CpuRegister.Rcx];
        if (pathListAddress == 0 || count == 0 || sizesAddress == 0 || count > 1024)
        {
            KernelRuntimeCompatExports.TrySetErrno(ctx, Einval);
            return (int)OrbisGen2Result.ORBIS_GEN2_ERROR_INVALID_ARGUMENT;
        }

        for (ulong i = 0; i < count; i++)
        {
            if (idsAddress != 0 &&
                !TryWriteUInt32Compat(ctx, idsAddress + (i * sizeof(uint)), uint.MaxValue))
            {
                KernelRuntimeCompatExports.TrySetErrno(ctx, Efault);
                return (int)OrbisGen2Result.ORBIS_GEN2_ERROR_MEMORY_FAULT;
            }

            if (!TryResolveAprFilepath(ctx, pathListAddress, i, out var guestPath))
            {
                KernelRuntimeCompatExports.TrySetErrno(ctx, Efault);
                return (int)OrbisGen2Result.ORBIS_GEN2_ERROR_MEMORY_FAULT;
            }

            var hostPath = ResolveGuestPath(guestPath);
            if (!TryGetAprFileSize(hostPath, out var fileSize))
            {
                // Per-file resolve: a missing entry gets an invalid id
                // (0xFFFFFFFF, already written above) and size 0, and the batch
                // CONTINUES. Aborting the whole batch on the first miss left the
                // remaining paths unresolved and could stall the guest's asset
                // streaming when a batch happens to include an absent (e.g.
                // patch/DLC) file; the caller checks per-file id/size.
                LogIoTrace("apr_resolve", guestPath, $"host='{hostPath}' index={i} count={count} result=not_found");
                if (sizesAddress != 0 &&
                    !TryWriteUInt64Compat(ctx, sizesAddress + (i * sizeof(ulong)), 0))
                {
                    KernelRuntimeCompatExports.TrySetErrno(ctx, Efault);
                    return (int)OrbisGen2Result.ORBIS_GEN2_ERROR_MEMORY_FAULT;
                }

                continue;
            }

            var fileId = AmprFileRegistry.Register(guestPath, hostPath);
            LogIoTrace("apr_resolve", guestPath, $"host='{hostPath}' index={i} count={count} id=0x{fileId:X8} size={fileSize}");

            if (idsAddress != 0 &&
                !TryWriteUInt32Compat(ctx, idsAddress + (i * sizeof(uint)), fileId))
            {
                KernelRuntimeCompatExports.TrySetErrno(ctx, Efault);
                return (int)OrbisGen2Result.ORBIS_GEN2_ERROR_MEMORY_FAULT;
            }

            if (!TryWriteUInt64Compat(ctx, sizesAddress + (i * sizeof(ulong)), fileSize))
            {
                KernelRuntimeCompatExports.TrySetErrno(ctx, Efault);
                return (int)OrbisGen2Result.ORBIS_GEN2_ERROR_MEMORY_FAULT;
            }
        }

        ctx[CpuRegister.Rax] = 0;
        return (int)OrbisGen2Result.ORBIS_GEN2_OK;
    }

    [SysAbiExport(
        Nid = "WT-5NKy42fw",
        ExportName = "sceKernelAprResolveFilepathsToIds",
        Target = Generation.Gen4 | Generation.Gen5,
        LibraryName = "libKernel")]
    public static int KernelAprResolveFilepathsToIds(CpuContext ctx)
    {
        var pathListAddress = ctx[CpuRegister.Rdi];
        var count = ctx[CpuRegister.Rsi];
        var idsAddress = ctx[CpuRegister.Rdx];
        if (pathListAddress == 0 || count == 0 || idsAddress == 0 || count > 1024)
        {
            KernelRuntimeCompatExports.TrySetErrno(ctx, Einval);
            return (int)OrbisGen2Result.ORBIS_GEN2_ERROR_INVALID_ARGUMENT;
        }

        for (ulong i = 0; i < count; i++)
        {
            if (!TryWriteUInt32Compat(ctx, idsAddress + (i * sizeof(uint)), uint.MaxValue))
            {
                KernelRuntimeCompatExports.TrySetErrno(ctx, Efault);
                return (int)OrbisGen2Result.ORBIS_GEN2_ERROR_MEMORY_FAULT;
            }

            if (!TryResolveAprFilepath(ctx, pathListAddress, i, out var guestPath))
            {
                KernelRuntimeCompatExports.TrySetErrno(ctx, Efault);
                return (int)OrbisGen2Result.ORBIS_GEN2_ERROR_MEMORY_FAULT;
            }

            var hostPath = ResolveGuestPath(guestPath);
            if (!TryGetAprFileSize(hostPath, out _))
            {
                LogIoTrace("apr_resolve_ids", guestPath, $"host='{hostPath}' index={i} count={count} result=not_found");
                KernelRuntimeCompatExports.TrySetErrno(ctx, 2);
                return (int)OrbisGen2Result.ORBIS_GEN2_ERROR_NOT_FOUND;
            }

            var fileId = AmprFileRegistry.Register(guestPath, hostPath);
            LogIoTrace("apr_resolve_ids", guestPath, $"host='{hostPath}' index={i} count={count} id=0x{fileId:X8}");

            if (!TryWriteUInt32Compat(ctx, idsAddress + (i * sizeof(uint)), fileId))
            {
                KernelRuntimeCompatExports.TrySetErrno(ctx, Efault);
                return (int)OrbisGen2Result.ORBIS_GEN2_ERROR_MEMORY_FAULT;
            }
        }

        ctx[CpuRegister.Rax] = 0;
        return (int)OrbisGen2Result.ORBIS_GEN2_OK;
    }

    [SysAbiExport(
        Nid = "ApkYaHb8Sek",
        ExportName = "sceKernelAprGetFileStat",
        Target = Generation.Gen4 | Generation.Gen5,
        LibraryName = "libKernel")]
    public static int KernelAprGetFileStat(CpuContext ctx)
    {
        var fileId = unchecked((uint)ctx[CpuRegister.Rdi]);
        var statAddress = ctx[CpuRegister.Rsi];
        if (statAddress == 0)
        {
            KernelRuntimeCompatExports.TrySetErrno(ctx, Einval);
            return (int)OrbisGen2Result.ORBIS_GEN2_ERROR_INVALID_ARGUMENT;
        }

        if (!AmprFileRegistry.TryGetHostPath(fileId, out var hostPath))
        {
            LogIoTrace("apr_get_file_stat", $"id=0x{fileId:X8}", "result=id_not_registered");
            KernelRuntimeCompatExports.TrySetErrno(ctx, 2);
            return (int)OrbisGen2Result.ORBIS_GEN2_ERROR_NOT_FOUND;
        }

        if (!TryWriteHostPathStat(ctx, statAddress, hostPath))
        {
            LogIoTrace("apr_get_file_stat", hostPath, $"id=0x{fileId:X8} result=not_found");
            KernelRuntimeCompatExports.TrySetErrno(ctx, 2);
            return (int)OrbisGen2Result.ORBIS_GEN2_ERROR_NOT_FOUND;
        }

        LogIoTrace("apr_get_file_stat", hostPath, $"id=0x{fileId:X8}");
        ctx[CpuRegister.Rax] = 0;
        return (int)OrbisGen2Result.ORBIS_GEN2_OK;
    }

    [SysAbiExport(
        Nid = "kBwCPsYX-m4",
        ExportName = "sceKernelFstat",
        Target = Generation.Gen4 | Generation.Gen5,
        LibraryName = "libKernel")]
    public static int KernelFstat(CpuContext ctx)
    {
        var fd = unchecked((int)ctx[CpuRegister.Rdi]);
        var statAddress = ctx[CpuRegister.Rsi];
        if (statAddress == 0)
        {
            return (int)OrbisGen2Result.ORBIS_GEN2_ERROR_INVALID_ARGUMENT;
        }

        if (!TryWriteOpenDescriptorStat(ctx, fd, statAddress))
        {
            return (int)OrbisGen2Result.ORBIS_GEN2_ERROR_NOT_FOUND;
        }

        ctx[CpuRegister.Rax] = 0;
        return (int)OrbisGen2Result.ORBIS_GEN2_OK;
    }

    [SysAbiExport(
        Nid = "AUXVxWeJU-A",
        ExportName = "sceKernelUnlink",
        Target = Generation.Gen4 | Generation.Gen5,
        LibraryName = "libKernel")]
    public static int KernelUnlink(CpuContext ctx)
    {
        var pathAddress = ctx[CpuRegister.Rdi];
        if (pathAddress == 0)
        {
            return (int)OrbisGen2Result.ORBIS_GEN2_ERROR_INVALID_ARGUMENT;
        }

        if (!TryReadNullTerminatedUtf8(ctx, pathAddress, MaxGuestStringLength, out var guestPath))
        {
            return (int)OrbisGen2Result.ORBIS_GEN2_ERROR_MEMORY_FAULT;
        }

        var hostPath = ResolveGuestPath(guestPath);
        if (IsReadOnlyGuestMutationPath(guestPath))
        {
            LogOpenTrace($"unlink readonly path='{guestPath}' host='{hostPath}'");
            return (int)OrbisGen2Result.ORBIS_GEN2_ERROR_PERMISSION_DENIED;
        }

        try
        {
            if (Directory.Exists(hostPath))
            {
                return (int)OrbisGen2Result.ORBIS_GEN2_ERROR_PERMISSION_DENIED;
            }

            if (!File.Exists(hostPath))
            {
                AddNegativeStatCacheForGuestPath(guestPath);
                return (int)OrbisGen2Result.ORBIS_GEN2_ERROR_NOT_FOUND;
            }

            File.Delete(hostPath);
            InvalidateNegativeStatCacheForPathAndAncestors(guestPath);
            InvalidateAprFileSizeCache(hostPath);
            AddNegativeStatCacheForGuestPath(guestPath);
            LogOpenTrace($"unlink path='{guestPath}' host='{hostPath}'");
            ctx[CpuRegister.Rax] = 0;
            return (int)OrbisGen2Result.ORBIS_GEN2_OK;
        }
        catch (UnauthorizedAccessException)
        {
            return (int)OrbisGen2Result.ORBIS_GEN2_ERROR_PERMISSION_DENIED;
        }
        catch (IOException)
        {
            return (int)OrbisGen2Result.ORBIS_GEN2_ERROR_BUSY;
        }
    }

    [SysAbiExport(
        Nid = "1-LFLmRFxxM",
        ExportName = "sceKernelMkdir",
        Target = Generation.Gen4 | Generation.Gen5,
        LibraryName = "libKernel")]
    public static int KernelMkdir(CpuContext ctx)
    {
        var pathAddress = ctx[CpuRegister.Rdi];
        if (pathAddress == 0)
        {
            return (int)OrbisGen2Result.ORBIS_GEN2_ERROR_INVALID_ARGUMENT;
        }

        if (!TryReadNullTerminatedUtf8(ctx, pathAddress, MaxGuestStringLength, out var guestPath))
        {
            return (int)OrbisGen2Result.ORBIS_GEN2_ERROR_MEMORY_FAULT;
        }

        var hostPath = ResolveGuestPath(guestPath);
        if (IsReadOnlyGuestMutationPath(guestPath))
        {
            LogOpenTrace($"mkdir readonly path='{guestPath}' host='{hostPath}'");
            return (int)OrbisGen2Result.ORBIS_GEN2_ERROR_PERMISSION_DENIED;
        }

        try
        {
            if (File.Exists(hostPath) || Directory.Exists(hostPath))
            {
                return (int)OrbisGen2Result.ORBIS_GEN2_ERROR_ALREADY_EXISTS;
            }

            var parentDirectory = Path.GetDirectoryName(hostPath);
            if (string.IsNullOrWhiteSpace(parentDirectory) || !Directory.Exists(parentDirectory))
            {
                return (int)OrbisGen2Result.ORBIS_GEN2_ERROR_NOT_FOUND;
            }

            Directory.CreateDirectory(hostPath);
            if (!Directory.Exists(hostPath))
            {
                return (int)OrbisGen2Result.ORBIS_GEN2_ERROR_NOT_FOUND;
            }

            InvalidateNegativeStatCacheForPathAndAncestors(guestPath);
            LogOpenTrace($"mkdir path='{guestPath}' host='{hostPath}'");
            ctx[CpuRegister.Rax] = 0;
            return (int)OrbisGen2Result.ORBIS_GEN2_OK;
        }
        catch (UnauthorizedAccessException)
        {
            return (int)OrbisGen2Result.ORBIS_GEN2_ERROR_PERMISSION_DENIED;
        }
        catch (IOException)
        {
            return (int)OrbisGen2Result.ORBIS_GEN2_ERROR_INVALID_ARGUMENT;
        }
    }

    [SysAbiExport(
        Nid = "naInUjYt3so",
        ExportName = "sceKernelRmdir",
        Target = Generation.Gen4 | Generation.Gen5,
        LibraryName = "libKernel")]
    public static int KernelRmdir(CpuContext ctx)
    {
        var pathAddress = ctx[CpuRegister.Rdi];
        if (pathAddress == 0)
        {
            return (int)OrbisGen2Result.ORBIS_GEN2_ERROR_INVALID_ARGUMENT;
        }

        if (!TryReadNullTerminatedUtf8(ctx, pathAddress, MaxGuestStringLength, out var guestPath))
        {
            return (int)OrbisGen2Result.ORBIS_GEN2_ERROR_MEMORY_FAULT;
        }

        var hostPath = ResolveGuestPath(guestPath);
        if (IsReadOnlyGuestMutationPath(guestPath))
        {
            LogOpenTrace($"rmdir readonly path='{guestPath}' host='{hostPath}'");
            return (int)OrbisGen2Result.ORBIS_GEN2_ERROR_PERMISSION_DENIED;
        }

        try
        {
            if (!Directory.Exists(hostPath))
            {
                AddNegativeStatCacheForGuestPath(guestPath);
                return (int)OrbisGen2Result.ORBIS_GEN2_ERROR_NOT_FOUND;
            }

            Directory.Delete(hostPath, recursive: false);
            InvalidateNegativeStatCacheForPathAndAncestors(guestPath);
            AddNegativeStatCacheForGuestPath(guestPath);
            LogOpenTrace($"rmdir path='{guestPath}' host='{hostPath}'");
            ctx[CpuRegister.Rax] = 0;
            return (int)OrbisGen2Result.ORBIS_GEN2_OK;
        }
        catch (UnauthorizedAccessException)
        {
            return (int)OrbisGen2Result.ORBIS_GEN2_ERROR_PERMISSION_DENIED;
        }
        catch (IOException)
        {
            return (int)OrbisGen2Result.ORBIS_GEN2_ERROR_BUSY;
        }
    }

    private static int KernelCloseCore(CpuContext ctx, int fd)
    {
        if (fd is 0 or 1 or 2)
        {
            ctx[CpuRegister.Rax] = 0;
            return (int)OrbisGen2Result.ORBIS_GEN2_OK;
        }

        FileStream? stream;
        lock (_fdGate)
        {
            if (_openFiles.Remove(fd, out stream))
            {
            }
            else if (_openDirectories.Remove(fd))
            {
                ctx[CpuRegister.Rax] = 0;
                return (int)OrbisGen2Result.ORBIS_GEN2_OK;
            }
            else
            {
                return (int)OrbisGen2Result.ORBIS_GEN2_ERROR_NOT_FOUND;
            }
        }

        stream.Dispose();
        ctx[CpuRegister.Rax] = 0;
        return (int)OrbisGen2Result.ORBIS_GEN2_OK;
    }

    [SysAbiExport(
        Nid = "DRuBt2pvICk",
        ExportName = "_read",
        Target = Generation.Gen4 | Generation.Gen5,
        LibraryName = "libKernel")]
    public static int KernelReadUnderscore(CpuContext ctx)
    {
        var fd = unchecked((int)ctx[CpuRegister.Rdi]);
        var bufferAddress = ctx[CpuRegister.Rsi];
        var requested = (int)Math.Min(ctx[CpuRegister.Rdx], int.MaxValue);
        if (requested < 0 || (requested > 0 && bufferAddress == 0))
        {
            return (int)OrbisGen2Result.ORBIS_GEN2_ERROR_INVALID_ARGUMENT;
        }

        if (requested == 0 || fd == 0)
        {
            ctx[CpuRegister.Rax] = 0;
            return (int)OrbisGen2Result.ORBIS_GEN2_OK;
        }

        FileStream? stream;
        lock (_fdGate)
        {
            _openFiles.TryGetValue(fd, out stream);
        }

        if (stream is null)
        {
            return (int)OrbisGen2Result.ORBIS_GEN2_ERROR_NOT_FOUND;
        }

        long positionBefore;
        try
        {
            positionBefore = stream.Position;
        }
        catch (IOException)
        {
            positionBefore = -1;
        }

        var buffer = GC.AllocateUninitializedArray<byte>(requested);
        var read = stream.Read(buffer, 0, requested);
        if (read > 0 && !ctx.Memory.TryWrite(bufferAddress, buffer.AsSpan(0, read)))
        {
            return (int)OrbisGen2Result.ORBIS_GEN2_ERROR_MEMORY_FAULT;
        }

        long positionAfter;
        try
        {
            positionAfter = stream.Position;
        }
        catch (IOException)
        {
            positionAfter = -1;
        }

        LogIoTrace(
            "read",
            stream.Name,
            $"fd={fd} req={requested} read={read} pos={positionBefore}->{positionAfter} preview='{PreviewIoBytes(buffer, read, 64)}' hex={PreviewIoHex(buffer, read, 32)} guest_tail={PreviewGuestHex(ctx, bufferAddress + (ulong)Math.Max(read, 0), 32)}");

        ctx[CpuRegister.Rax] = unchecked((ulong)read);
        return (int)OrbisGen2Result.ORBIS_GEN2_OK;
    }

    [SysAbiExport(
        Nid = "AqBioC2vF3I",
        ExportName = "read",
        Target = Generation.Gen4 | Generation.Gen5,
        LibraryName = "libKernel")]
    public static int PosixRead(CpuContext ctx) => KernelReadUnderscore(ctx);

    [SysAbiExport(
        Nid = "Cg4srZ6TKbU",
        ExportName = "sceKernelRead",
        Target = Generation.Gen4 | Generation.Gen5,
        LibraryName = "libKernel")]
    public static int KernelRead(CpuContext ctx) => KernelReadUnderscore(ctx);

    [SysAbiExport(
        Nid = "Oy6IpwgtYOk",
        ExportName = "lseek",
        Target = Generation.Gen4 | Generation.Gen5,
        LibraryName = "libKernel")]
    public static int PosixLseek(CpuContext ctx)
    {
        var result = KernelLseekCore(
            unchecked((int)ctx[CpuRegister.Rdi]),
            unchecked((long)ctx[CpuRegister.Rsi]),
            unchecked((int)ctx[CpuRegister.Rdx]),
            out var position);

        if (result != OrbisGen2Result.ORBIS_GEN2_OK)
        {
            ctx[CpuRegister.Rax] = ulong.MaxValue;
            return (int)OrbisGen2Result.ORBIS_GEN2_OK;
        }

        ctx[CpuRegister.Rax] = unchecked((ulong)position);
        return (int)OrbisGen2Result.ORBIS_GEN2_OK;
    }

    [SysAbiExport(
        Nid = "oib76F-12fk",
        ExportName = "sceKernelLseek",
        Target = Generation.Gen4 | Generation.Gen5,
        LibraryName = "libKernel")]
    public static int KernelLseek(CpuContext ctx)
    {
        var result = KernelLseekCore(
            unchecked((int)ctx[CpuRegister.Rdi]),
            unchecked((long)ctx[CpuRegister.Rsi]),
            unchecked((int)ctx[CpuRegister.Rdx]),
            out var position);

        if (result != OrbisGen2Result.ORBIS_GEN2_OK)
        {
            return (int)result;
        }

        ctx[CpuRegister.Rax] = unchecked((ulong)position);
        return (int)OrbisGen2Result.ORBIS_GEN2_OK;
    }

    [SysAbiExport(
        Nid = "taRWhTJFTgE",
        ExportName = "sceKernelGetdirentries",
        Target = Generation.Gen4 | Generation.Gen5,
        LibraryName = "libKernel")]
    public static int KernelGetdirentries(CpuContext ctx)
    {
        return KernelGetdirentriesCore(
            ctx,
            unchecked((int)ctx[CpuRegister.Rdi]),
            ctx[CpuRegister.Rsi],
            unchecked((int)Math.Min(ctx[CpuRegister.Rdx], int.MaxValue)),
            ctx[CpuRegister.Rcx]);
    }

    [SysAbiExport(
        Nid = "j2AIqSqJP0w",
        ExportName = "sceKernelGetdents",
        Target = Generation.Gen4 | Generation.Gen5,
        LibraryName = "libKernel")]
    public static int KernelGetdents(CpuContext ctx)
    {
        return KernelGetdirentriesCore(
            ctx,
            unchecked((int)ctx[CpuRegister.Rdi]),
            ctx[CpuRegister.Rsi],
            unchecked((int)Math.Min(ctx[CpuRegister.Rdx], int.MaxValue)),
            0);
    }

    private static OrbisGen2Result KernelLseekCore(int fd, long offset, int whence, out long position)
    {
        position = -1;

        FileStream? stream;
        lock (_fdGate)
        {
            _openFiles.TryGetValue(fd, out stream);
        }

        if (stream is null)
        {
            LogIoTrace("lseek", $"fd:{fd}", $"offset={offset} whence={whence} result=badfd");
            return OrbisGen2Result.ORBIS_GEN2_ERROR_NOT_FOUND;
        }

        SeekOrigin origin;
        switch (whence)
        {
            case SeekSet:
                origin = SeekOrigin.Begin;
                break;
            case SeekCur:
                origin = SeekOrigin.Current;
                break;
            case SeekEnd:
                origin = SeekOrigin.End;
                break;
            default:
                LogIoTrace("lseek", stream.Name, $"fd={fd} offset={offset} whence={whence} result=invalid_whence");
                return OrbisGen2Result.ORBIS_GEN2_ERROR_INVALID_ARGUMENT;
        }

        try
        {
            position = stream.Seek(offset, origin);
        }
        catch (IOException ex)
        {
            LogIoTrace("lseek", stream.Name, $"fd={fd} offset={offset} whence={whence} result=io_error ex={ex.Message}");
            return OrbisGen2Result.ORBIS_GEN2_ERROR_INVALID_ARGUMENT;
        }
        catch (ArgumentException ex)
        {
            LogIoTrace("lseek", stream.Name, $"fd={fd} offset={offset} whence={whence} result=invalid ex={ex.Message}");
            return OrbisGen2Result.ORBIS_GEN2_ERROR_INVALID_ARGUMENT;
        }

        LogIoTrace("lseek", stream.Name, $"fd={fd} offset={offset} whence={whence} pos={position}");
        return OrbisGen2Result.ORBIS_GEN2_OK;
    }

    [SysAbiExport(
        Nid = "FxVZqBAA7ks",
        ExportName = "_write",
        Target = Generation.Gen4 | Generation.Gen5,
        LibraryName = "libKernel")]
    public static int KernelWriteUnderscore(CpuContext ctx)
    {
        var fd = unchecked((int)ctx[CpuRegister.Rdi]);
        var bufferAddress = ctx[CpuRegister.Rsi];
        var requested = (int)Math.Min(ctx[CpuRegister.Rdx], int.MaxValue);
        if (requested < 0 || (requested > 0 && bufferAddress == 0))
        {
            return (int)OrbisGen2Result.ORBIS_GEN2_ERROR_INVALID_ARGUMENT;
        }

        var payload = requested == 0
            ? Array.Empty<byte>()
            : GC.AllocateUninitializedArray<byte>(requested);
        if (requested > 0 && !ctx.Memory.TryRead(bufferAddress, payload))
        {
            return (int)OrbisGen2Result.ORBIS_GEN2_ERROR_MEMORY_FAULT;
        }

        if (fd == 1 || fd == 2)
        {
            var text = Encoding.UTF8.GetString(payload);
            if (fd == 1)
            {
                Console.Out.Write(text);
                Console.Out.Flush();
            }
            else
            {
                Console.Error.Write(text);
                Console.Error.Flush();
            }

            ctx[CpuRegister.Rax] = unchecked((ulong)requested);
            return (int)OrbisGen2Result.ORBIS_GEN2_OK;
        }

        FileStream? stream;
        lock (_fdGate)
        {
            _openFiles.TryGetValue(fd, out stream);
        }

        if (stream is null)
        {
            return (int)OrbisGen2Result.ORBIS_GEN2_ERROR_NOT_FOUND;
        }

        stream.Write(payload, 0, requested);
        stream.Flush();
        ctx[CpuRegister.Rax] = unchecked((ulong)requested);
        return (int)OrbisGen2Result.ORBIS_GEN2_OK;
    }

    [SysAbiExport(
        Nid = "FN4gaPmuFV8",
        ExportName = "write",
        Target = Generation.Gen4 | Generation.Gen5,
        LibraryName = "libKernel")]
    public static int PosixWrite(CpuContext ctx) => KernelWriteUnderscore(ctx);

    [SysAbiExport(
        Nid = "4wSze92BhLI",
        ExportName = "sceKernelWrite",
        Target = Generation.Gen4 | Generation.Gen5,
        LibraryName = "libKernel")]
    public static int KernelWrite(CpuContext ctx) => KernelWriteUnderscore(ctx);

    [SysAbiExport(
        Nid = "lLMT9vJAck0",
        ExportName = "clock_gettime",
        Target = Generation.Gen4 | Generation.Gen5,
        LibraryName = "libKernel")]
    public static int ClockGettime(CpuContext ctx)
    {
        var timespecAddress = ctx[CpuRegister.Rsi];
        if (timespecAddress == 0)
        {
            return (int)OrbisGen2Result.ORBIS_GEN2_ERROR_INVALID_ARGUMENT;
        }

        var now = DateTimeOffset.UtcNow;
        var seconds = now.ToUnixTimeSeconds();
        var nanoseconds = (now.Ticks % TimeSpan.TicksPerSecond) * 100;
        if (!ctx.TryWriteUInt64(timespecAddress, unchecked((ulong)seconds)) ||
            !ctx.TryWriteUInt64(timespecAddress + sizeof(long), unchecked((ulong)nanoseconds)))
        {
            return (int)OrbisGen2Result.ORBIS_GEN2_ERROR_MEMORY_FAULT;
        }

        ctx[CpuRegister.Rax] = 0;
        return (int)OrbisGen2Result.ORBIS_GEN2_OK;
    }

    [SysAbiExport(
        Nid = "vNe1w4diLCs",
        ExportName = "__tls_get_addr",
        Target = Generation.Gen4 | Generation.Gen5,
        LibraryName = "libKernel")]
    public static int TlsGetAddr(CpuContext ctx)
    {
        var tlsInfoAddress = ctx[CpuRegister.Rdi];
        if (tlsInfoAddress == 0)
        {
            return (int)OrbisGen2Result.ORBIS_GEN2_ERROR_INVALID_ARGUMENT;
        }

        if (!ctx.TryReadUInt64(tlsInfoAddress, out var moduleId) ||
            !ctx.TryReadUInt64(tlsInfoAddress + sizeof(ulong), out var offset))
        {
            return (int)OrbisGen2Result.ORBIS_GEN2_ERROR_MEMORY_FAULT;
        }

        ctx[CpuRegister.Rax] = ResolveTlsAddress(ctx, moduleId, offset);
        return (int)OrbisGen2Result.ORBIS_GEN2_OK;
    }

    private static ulong ResolveTlsAddress(CpuContext ctx, ulong moduleId, ulong offset)
    {
        return SharpEmu.HLE.GuestTlsTemplate.ResolveAddress(ctx, moduleId, offset);
    }

    [SysAbiExport(
        Nid = "pB-yGZ2nQ9o",
        ExportName = "_sceKernelSetThreadAtexitCount",
        Target = Generation.Gen4 | Generation.Gen5,
        LibraryName = "libKernel")]
    public static int KernelSetThreadAtexitCount(CpuContext ctx)
    {
        _threadAtexitCountCallback = ctx[CpuRegister.Rdi];
        return (int)OrbisGen2Result.ORBIS_GEN2_OK;
    }

    [SysAbiExport(
        Nid = "WhCc1w3EhSI",
        ExportName = "_sceKernelSetThreadAtexitReport",
        Target = Generation.Gen4 | Generation.Gen5,
        LibraryName = "libKernel")]
    public static int KernelSetThreadAtexitReport(CpuContext ctx)
    {
        _threadAtexitReportCallback = ctx[CpuRegister.Rdi];
        return (int)OrbisGen2Result.ORBIS_GEN2_OK;
    }

    [SysAbiExport(
        Nid = "rNhWz+lvOMU",
        ExportName = "_sceKernelSetThreadDtors",
        Target = Generation.Gen4 | Generation.Gen5,
        LibraryName = "libKernel")]
    public static int KernelSetThreadDtors(CpuContext ctx)
    {
        _threadDtorsCallback = ctx[CpuRegister.Rdi];
        return (int)OrbisGen2Result.ORBIS_GEN2_OK;
    }

    public static void RunThreadDtors(CpuContext ctx)
    {
        var callback = _threadDtorsCallback;
        if (callback == 0)
        {
            return;
        }

        _ = GuestThreadExecution.Scheduler?.TryCallGuestFunction(
            ctx,
            callback,
            0,
            0,
            0,
            0,
            "kernel_thread_dtors",
            out _);
    }

    [SysAbiExport(
        Nid = "Tz4RNUCBbGI",
        ExportName = "_sceKernelRtldThreadAtexitIncrement",
        Target = Generation.Gen4 | Generation.Gen5,
        LibraryName = "libKernel")]
    public static int KernelRtldThreadAtexitIncrement(CpuContext ctx)
    {
        return KernelRtldThreadAtexitAdjust(ctx, delta: +1);
    }

    [SysAbiExport(
        Nid = "8OnWXlgQlvo",
        ExportName = "_sceKernelRtldThreadAtexitDecrement",
        Target = Generation.Gen4 | Generation.Gen5,
        LibraryName = "libKernel")]
    public static int KernelRtldThreadAtexitDecrement(CpuContext ctx)
    {
        return KernelRtldThreadAtexitAdjust(ctx, delta: -1);
    }

    [SysAbiExport(
        Nid = "pO96TwzOm5E",
        ExportName = "sceKernelGetDirectMemorySize",
        Target = Generation.Gen4 | Generation.Gen5,
        LibraryName = "libKernel")]
    public static int KernelGetDirectMemorySize(CpuContext ctx)
    {
        ctx[CpuRegister.Rax] = DirectMemorySizeBytes;
        return (int)OrbisGen2Result.ORBIS_GEN2_OK;
    }

    [SysAbiExport(
        Nid = "C0f7TJcbfac",
        ExportName = "sceKernelAvailableDirectMemorySize",
        Target = Generation.Gen4 | Generation.Gen5,
        LibraryName = "libKernel")]
    public static int KernelAvailableDirectMemorySize(CpuContext ctx)
    {
        var arg0 = ctx[CpuRegister.Rdi];
        var arg1 = ctx[CpuRegister.Rsi];
        var arg2 = ctx[CpuRegister.Rdx];
        var arg3 = ctx[CpuRegister.Rcx];
        var arg4 = ctx[CpuRegister.R8];

        ulong used = 0;
        lock (_memoryGate)
        {
            foreach (var allocation in _directAllocations.Values)
            {
                used = Math.Min(DirectMemorySizeBytes, used + allocation.Length);
            }
        }

        var totalAvailable = used >= DirectMemorySizeBytes
            ? 0UL
            : DirectMemorySizeBytes - used;

        if (arg1 != 0 || arg2 != 0 || arg3 != 0 || arg4 != 0)
        {
            var searchStartRaw = unchecked((long)arg0);
            var searchEndRaw = unchecked((long)arg1);
            var alignment = arg2 == 0 ? 0x1000UL : arg2;
            var outAddress = arg3;
            var outSize = arg4;
            if (outAddress == 0 || outSize == 0)
            {
                return (int)OrbisGen2Result.ORBIS_GEN2_ERROR_INVALID_ARGUMENT;
            }

            var searchStart = searchStartRaw < 0 ? 0UL : (ulong)searchStartRaw;
            var searchEnd = searchEndRaw <= 0
                ? DirectMemorySizeBytes
                : Math.Min((ulong)searchEndRaw, DirectMemorySizeBytes);
            if (searchStart >= searchEnd)
            {
                return (int)OrbisGen2Result.ORBIS_GEN2_ERROR_INVALID_ARGUMENT;
            }

            if (!TryFindAvailableDirectMemorySpanLocked(searchStart, searchEnd, alignment, out var candidate, out var rangeAvailable))
            {
                return (int)OrbisGen2Result.ORBIS_GEN2_ERROR_NOT_FOUND;
            }

            if (!ctx.TryWriteUInt64(outAddress, candidate) || !ctx.TryWriteUInt64(outSize, rangeAvailable))
            {
                return (int)OrbisGen2Result.ORBIS_GEN2_ERROR_MEMORY_FAULT;
            }

            return (int)OrbisGen2Result.ORBIS_GEN2_OK;
        }

        var outSizeAddress = arg0;
        if (outSizeAddress == 0)
        {
            return (int)OrbisGen2Result.ORBIS_GEN2_ERROR_INVALID_ARGUMENT;
        }

        if (!ctx.TryWriteUInt64(outSizeAddress, totalAvailable))
        {
            return (int)OrbisGen2Result.ORBIS_GEN2_ERROR_MEMORY_FAULT;
        }

        return (int)OrbisGen2Result.ORBIS_GEN2_OK;
    }

    [SysAbiExport(
        Nid = "aNz11fnnzi4",
        ExportName = "sceKernelAvailableFlexibleMemorySize",
        Target = Generation.Gen4 | Generation.Gen5,
        LibraryName = "libKernel")]
    public static int KernelAvailableFlexibleMemorySize(CpuContext ctx)
    {
        var outSizeAddress = ctx[CpuRegister.Rdi];
        if (outSizeAddress == 0)
        {
            return (int)OrbisGen2Result.ORBIS_GEN2_ERROR_INVALID_ARGUMENT;
        }

        ulong available;
        lock (_memoryGate)
        {
            available = _allocatedFlexibleBytes >= FlexibleMemorySizeBytes
                ? 0
                : FlexibleMemorySizeBytes - _allocatedFlexibleBytes;
        }

        if (!ctx.TryWriteUInt64(outSizeAddress, available))
        {
            return (int)OrbisGen2Result.ORBIS_GEN2_ERROR_MEMORY_FAULT;
        }

        return (int)OrbisGen2Result.ORBIS_GEN2_OK;
    }

    [SysAbiExport(
        Nid = "rTXw65xmLIA",
        ExportName = "sceKernelAllocateDirectMemory",
        Target = Generation.Gen4 | Generation.Gen5,
        LibraryName = "libKernel")]
    public static int KernelAllocateDirectMemory(CpuContext ctx)
    {
        var searchStartRaw = unchecked((long)ctx[CpuRegister.Rdi]);
        var searchEndRaw = unchecked((long)ctx[CpuRegister.Rsi]);
        var length = ctx[CpuRegister.Rdx];
        var alignment = ctx[CpuRegister.Rcx];
        var memoryType = unchecked((int)ctx[CpuRegister.R8]);
        var outAddress = ctx[CpuRegister.R9];

        if (length == 0 || outAddress == 0)
        {
            TraceDirectMemoryCall(
                ctx,
                "allocate_direct",
                length,
                alignment,
                memoryType,
                outAddress,
                result: OrbisGen2Result.ORBIS_GEN2_ERROR_INVALID_ARGUMENT);
            return (int)OrbisGen2Result.ORBIS_GEN2_ERROR_INVALID_ARGUMENT;
        }

        var limit = DirectMemorySizeBytes;
        ulong searchStart;
        ulong searchEnd;

        if (searchEndRaw <= 0)
        {
            searchEnd = limit;
        }
        else
        {
            searchEnd = (ulong)searchEndRaw;
            if (searchEnd > limit)
            {
                searchEnd = limit;
            }
        }

        if (searchStartRaw < 0)
        {
            searchStart = 0;
        }
        else
        {
            searchStart = (ulong)searchStartRaw;
        }

        if (searchStart >= searchEnd)
        {
            searchStart = 0;
        }

        // PS5 direct memory is allocated in 16 KiB pages; when the guest does
        // not care about alignment, default to that granularity rather than the
        // host 4 KiB page so physical offsets stay on true page boundaries.
        var align = alignment == 0 ? OrbisPageSize : alignment;
        ulong selectedAddress;
        lock (_memoryGate)
        {
            if (!TryAllocateDirectMemoryLocked(searchStart, searchEnd, length, align, memoryType, DirectMemorySizeBytes, out selectedAddress))
            {
                TraceDirectMemoryCall(
                    ctx,
                    "allocate_direct",
                    length,
                    align,
                    memoryType,
                    outAddress,
                    result: OrbisGen2Result.ORBIS_GEN2_ERROR_TRY_AGAIN);
                return (int)OrbisGen2Result.ORBIS_GEN2_ERROR_TRY_AGAIN;
            }
        }

        if (!ctx.TryWriteUInt64(outAddress, selectedAddress))
        {
            TraceDirectMemoryCall(
                ctx,
                "allocate_direct",
                length,
                align,
                memoryType,
                outAddress,
                selectedAddress,
                OrbisGen2Result.ORBIS_GEN2_ERROR_MEMORY_FAULT);
            return (int)OrbisGen2Result.ORBIS_GEN2_ERROR_MEMORY_FAULT;
        }

        TraceDirectMemoryCall(
            ctx,
            "allocate_direct",
            length,
            align,
            memoryType,
            outAddress,
            selectedAddress,
            OrbisGen2Result.ORBIS_GEN2_OK);

        return (int)OrbisGen2Result.ORBIS_GEN2_OK;
    }

    [SysAbiExport(
        Nid = "B+vc2AO2Zrc",
        ExportName = "sceKernelAllocateMainDirectMemory",
        Target = Generation.Gen4 | Generation.Gen5,
        LibraryName = "libKernel")]
    public static int KernelAllocateMainDirectMemory(CpuContext ctx)
    {
        var length = ctx[CpuRegister.Rdi];
        var alignment = ctx[CpuRegister.Rsi];
        var memoryType = unchecked((int)ctx[CpuRegister.Rdx]);
        var outAddress = ctx[CpuRegister.Rcx];
        if (outAddress == 0 || length == 0)
        {
            TraceDirectMemoryCall(
                ctx,
                "allocate_main_direct",
                length,
                alignment,
                memoryType,
                outAddress,
                result: OrbisGen2Result.ORBIS_GEN2_ERROR_INVALID_ARGUMENT);
