module ExtendedIntegers

export FlexibleUInt, FixedUInt

using Base: BitUnsigned, front, tail, fill_to_length

include("bits.jl")
include("vectors.jl")
include("tuples.jl")

## FixedUInt
##============
struct FixedUInt{N,U<:BitUnsigned} <: Unsigned
    parts::NTuple{N,U}
end
function FixedUInt{N,U}(a::Unsigned) where {N, U<:BitUnsigned}
    t = fill_to_length((), zero(U), Val{N})
    t = _tfill(t, a)
    return FixedUInt{N,U}(t)
end
function Base.show(io::IO, a::FixedUInt{N}) where {N}
    print(io,"0x")
    for k = N:-1:1
        print(io, " ", repr(a.parts[k])[3:end])
    end
end

# zero and one
Base.iszero(a::FixedUInt) = all(iszero, a.parts)
Base.zero(::Type{FixedUInt{N, U}}) where {N, U<:BitUnsigned} =
    FixedUInt{N, U}(fill_to_length((), zero(U), Val{N}))
Base.one(::Type{FixedUInt{N, U}}) where {N, U<:BitUnsigned} =
    FixedUInt{N, U}(fill_to_length((one(U),), zero(U), Val{N}))

# comparison
Base.:<(a1::F, a2::F) where {F<:FixedUInt} = _tcmp(a1.parts, a2.parts) < 0
Base.:<=(a1::F, a2::F) where {F<:FixedUInt} = _tcmp(a1.parts, a2.parts) <= 0

# bit manipulation
Base.:<<(a::F, n::UInt) where {F<:FixedUInt} = F(_tleftshift(a.parts, n))
Base.:>>(a::F, n::UInt) where {F<:FixedUInt} = F(_trightshift(a.parts, n))
Base.:>>>(a::FixedUInt, n::UInt) = >>(a, n)
Base.:&(a1::F, a2::F) where {F<:FixedUInt} = F(_tand(a1.parts, a2.parts))
Base.:|(a1::F, a2::F) where {F<:FixedUInt} = F(_tor(a1.parts, a2.parts))
Base.:~(a::FixedUInt) = F(_tnot(a.parts))

# arithmitic
Base.:+(a1::F, a2::F) where {F<:FixedUInt} = F(_tadd(a1.parts, a2.parts))
Base.:-(a1::F, a2::F) where {F<:FixedUInt} = F(_tsub(a1.parts, a2.parts))
Base.:*(a1::F, a2::F) where {F<:FixedUInt} = F(_tmul(a1.parts, a2.parts))
Base.divrem(n::F, d::F) where {F<:FixedUInt} = map(F, _tdivrem(n.parts, d.parts))

## FlexibleUInt
##===============
struct FlexibleUInt{U<:BitUnsigned} <: Unsigned
    parts::Vector{U}
end
function FlexibleUInt{U}(a::Unsigned) where {U<:BitUnsigned}
    x = U[]
    while !iszero(a)
        push!(x, convert(U, a & typemax(U)))
        a >>= fullshift(U)
    end
    return FlexibleUInt{U}(x)
end
function Base.show(io::IO, a::FlexibleUInt)
    print(io,"0x")
    for k = length(a.parts):-1:1
        print(io, " ", repr(a.parts[k])[3:end])
    end
end

Base.promote_rule(F::Type{<:FlexibleUInt}, ::Type{<:BitUnsigned}) = F
Base.promote_rule(::Type{FlexibleUInt{U1}}, ::Type{FlexibleUInt{U2}}) where {U1<:BitUnsigned,U2<:BitUnsigned} = FlexibleUInt{promote_type(U1,U2)}

Base.convert(::Type{F}, a::F) where {F<:FlexibleUInt} = a
Base.convert(F::Type{<:FlexibleUInt}, a::Unsigned) = F(a)
Base.convert(F::Type{<:FlexibleUInt}, a::Signed) = F(convert(Unsigned, a))
function Base.convert(::Type{U}, a::FlexibleUInt{V}) where {U<:BitUnsigned, V<:BitUnsigned}
    b = zero(U)
    x = a.parts
    shift = 0
    for k = 1:length(x)
        db = convert(U, x[k])
        leading_zeros(db) < shift && throw(InexactError())
        b += (db << shift)
        shift += fullshift(V)
    end
    return b
end

# zero and one
Base.iszero(a::FlexibleUInt) = length(a.parts) == 0 # quick test
Base.zero(::Type{FlexibleUInt{U}}) where {U<:BitUnsigned} = FlexibleUInt{U}(U[])
Base.one(::Type{FlexibleUInt{U}}) where {U<:BitUnsigned} = FlexibleUInt{U}([one(U)])

# comparison
Base.:<(a1::FlexibleUInt{U}, a2::FlexibleUInt{U}) where {U<:Unsigned} = _vcmp(a1.parts, a2.parts) < 0
Base.:<=(a1::FlexibleUInt{U}, a2::FlexibleUInt{U}) where {U<:Unsigned} = _vcmp(a1.parts, a2.parts) <= 0
Base.:(==)(a1::FlexibleUInt{U}, a2::FlexibleUInt{U}) where {U<:Unsigned} = a1.parts == a2.parts

# bit manipulation
Base.:<<(a::F, n::UInt) where {F<:FlexibleUInt} = F(_vleftshift!(copy(a.parts), n))
Base.:>>(a::F, n::UInt) where {F<:FlexibleUInt} = F(_vrightshift!(copy(a.parts), n))
Base.:>>>(a::FlexibleUInt, n::UInt) = >>(a, n)
Base.:&(a1::F, a2::F) where {F<:FlexibleUInt} =
    length(a1.parts) > length(a2.parts) ? F(_vand!(copy(a2.parts), a1.parts)) :
                                            F(_vand!(copy(a1.parts), a2.parts))
Base.:|(a1::F, a2::F) where {F<:FlexibleUInt} =
    length(a1.parts) > length(a2.parts) ? F(_vor!(copy(a1.parts), a2.parts)) :
                                            F(_vor!(copy(a2.parts), a1.parts))

# arithmitic
Base.:+(a1::F, a2::F) where {F<:FlexibleUInt} =
    length(a1.parts) > length(a2.parts) ? F(_vadd!(copy(a1.parts), a2.parts)) :
                                        F(_vadd!(copy(a2.parts), a1.parts))
Base.:-(a1::F, a2::F) where {F<:FlexibleUInt} =
    a2 <= a1 ? F(_vsub!(copy(a1.parts), a2.parts)) : throw(OverflowError())
Base.:*(a1::F, a2::F) where {U,F<:FlexibleUInt{U}} =
    F(_vmuladd!(fill(zero(U), length(a1.parts)+length(a2.parts)), a1.parts, a2.parts))
Base.divrem(n::F, d::F) where {F<:FlexibleUInt} = map(F, _vdivrem!(copy(n.parts), d.parts))

end # module
