// Copyright (C) 2026 SharpEmu Emulator Project
// SPDX-License-Identifier: GPL-2.0-or-later

using SharpEmu.HLE;
using System;
using System.Diagnostics.CodeAnalysis;
using SharpEmu.Logging;

namespace SharpEmu.Libs.Kernel;

internal static class KernelVirtualRangeAllocator
{
    private static readonly SharpEmuLogger Log = SharpEmuLog.For("Libs.Kernel");
    public static bool TryReserve(
        CpuContext ctx,
        ulong desiredAddress,
        ulong length,
        bool executable,
        ulong alignment,
        bool allowSearch,
        bool allowAllocateAtAlternative,
        string traceName,
        out ulong mappedAddress)
    {
        mappedAddress = 0;
        if (length == 0)
        {
            return false;
        }

        try
        {
            if (!TryResolveAddressSpace(ctx.Memory, out var addressSpace))
            {
                Log.Trace($"{traceName}: AllocateAt missing on {ctx.Memory.GetType().FullName}");
                return false;
            }

            if (allowSearch &&
                addressSpace.TryAllocateAtOrAbove(desiredAddress, length, executable, alignment, out var searchedAddress) &&
                searchedAddress != 0)
            {
                mappedAddress = searchedAddress;
                return true;
            }

            var allocated = addressSpace.AllocateAt(desiredAddress, length, executable, allowAllocateAtAlternative);
            if (allocated == 0)
            {
                Log.Trace($"{traceName}: AllocateAt returned {typeof(ulong).FullName} value=0");
                return false;
            }

            mappedAddress = allocated;
            return true;
        }
        catch
        {
            // Expected when a fixed-address request cannot be satisfied on
            // this host; the caller falls back or reports the failure.
            Log.Trace($"{traceName}: no host mapping at 0x{desiredAddress:X16} len=0x{length:X}");
            return false;
        }
    }

    /// <summary>
    /// Finds the <see cref="IGuestAddressSpace"/> behind <paramref name="rootMemory"/>,
    /// unwrapping decorators (bounded, like the reflection walker this replaced).
    /// </summary>
    public static bool TryResolveAddressSpace(ICpuMemory rootMemory, [NotNullWhen(true)] out IGuestAddressSpace? addressSpace)
    {
        var target = rootMemory;
        for (var depth = 0; depth < 4; depth++)
        {
            if (target is IGuestAddressSpace resolved)
            {
                addressSpace = resolved;
                return true;
            }

            if (target is not ICpuMemoryWrapper wrapper)
            {
                break;
            }

            var inner = wrapper.Inner;
            if (inner is null || ReferenceEquals(inner, target))
            {
                break;
            }

            target = inner;
        }

        addressSpace = null;
        return false;
    }
}