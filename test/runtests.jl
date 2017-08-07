using ExtendedIntegers
using Base.Test

import ExtendedIntegers: _mul, _mul2, _divrem, _divrem2, _estimateq, fullshift
# random tests
const F = FlexibleUInt{UInt8}
for k in 1:100000
    a = rand(UInt64)
    # convert
    @test convert(UInt64, convert(F, a)) == a
    # left shift
    for s = 0:64
        @test convert(F, a >> s) == convert(F, a) >> s
    end
    # right shift
    a = UInt64(rand(UInt32))
    for s = 0:32
        @test convert(F, a << s) == convert(F, a) << s
    end
    # bitwise and an or
    a = rand(UInt64)
    b = rand(UInt32)
    @test convert(F, a & b) == convert(F,a) & convert(F,b)
    @test convert(F, a | b) == convert(F,a) | convert(F,b)
    # add
    a = rand(UInt64)>>1
    b = rand(UInt64)>>1
    @test convert(F, a + b) == convert(F,a) + convert(F,b)
    # subtract
    a = rand(UInt64)
    b = rand(zero(a):a)
    @test convert(F, a - b) == convert(F,a) - convert(F,b)
    # mul
    a = rand(UInt32)
    b = rand(UInt32)
    @test convert(F, widen(a)*widen(b)) == convert(F,a) * convert(F,b)
    # div
for k in 1:10000
    a = rand(UInt64)
    b = rand(UInt32)
    @test map(F, divrem(a,b)) == divrem(convert(F,a), convert(F,b))
end

#
# U = UInt8
# for a in zero(U):typemax(U), b in zero(U):typemax(U)
#     @test _mul(a,b) == _mul2(a,b)
# end
# for a0 in zero(U):typemax(U), d in one(U):typemax(U)
#     for a1 in zero(U):(d-one(U))
#         @test _divrem(a0,a1,d) == _divrem2(a0,a1,d)
#     end
# end

U = UInt8
for k in 1:1000000
    v = rand((typemax(U)>>1+one(U)):typemax(U))
    u′′, u′, v′ = rand(U,4)
    if  v′ > u′
        u = rand(zero(U):v)
    else
        u = rand(zero(U):(v-one(v)))
    end
    num = UInt64(u)<<(2*fullshift(U)) + UInt64(u′)<<fullshift(U) + UInt64(u′′)
    den = UInt64(v)<<fullshift(U) + UInt64(v′)
    @test div(num,den) == _estimateq(u′′,u′,u,v′,v)
end

for k in 1:10000
    a = rand(UInt64)
    b = rand(UInt64)
    @test convert(F, a & b) == convert(F, a) & convert(F, b)
    @test convert(F, a | b) == convert(F, a) | convert(F, b)
    a >>= 1
    b >>= 1
    @test convert(F, a + b) == convert(F, a) + convert(F, b)
    a = rand(UInt64)
    b = rand(zero(a):a)
    @test convert(F, a - b) == convert(F, a) - convert(F, b)
    a = UInt64(rand(UInt32))
    b = UInt64(rand(UInt32))
    @test convert(F, a * b) == convert(F, a) * convert(F, b)
end


# write your own tests here
# const T = UInt16
# for k in UInt16(0):typemax(T)
#     @test k == convert(T, convert(FlexibleUInt{UInt8},k))
#     @test k == convert(T, convert(FlexibleUInt{UInt16},k))
#     @test k == convert(T, convert(FlexibleUInt{UInt32},k))
#     @test k == convert(T, convert(FlexibleUInt{UInt64},k))
#
#     @test k == convert(UInt32, convert(FlexibleUInt{UInt8},k))
#     @test k == convert(UInt64, convert(FlexibleUInt{UInt8},k))
#
#
# end
