module ExtendedIntegers

export FlexibleUInt, FixedUInt

using Base: BitUnsigned, front, tail, fill_to_length, setindex

include("bits.jl")
include("vectors.jl")
include("tuples.jl")

## FixedUInt
##============
struct FixedUInt{N,U<:BitUnsigned} <: Unsigned
    parts::NTuple{N,U}
end
function FixedUInt{N,U}(a::BitUnsigned) where {N, U<:BitUnsigned}
    t = fill_to_length((), zero(U), Val{N})
    t = _tfill(t, a)
    return FixedUInt{N,U}(t)
end
FixedUInt{N,U}(a::FixedUInt{N,U}) where {N, U<:BitUnsigned} = a

function Base.show(io::IO, a::FixedUInt{N}) where {N}
    print(io,"0x")
    for k = N:-1:1
        print(io, " ", repr(a.parts[k])[3:end])
    end
end

Base.promote_rule(F::Type{<:FixedUInt}, ::Type{<:Signed}) = F
Base.promote_rule(F::Type{<:FixedUInt}, ::Type{<:BitUnsigned}) = F
Base.promote_rule(::Type{FixedUInt{N,U1}}, ::Type{FixedUInt{N,U2}}) where {N,U1<:BitUnsigned,U2<:BitUnsigned} = FixedUInt{N,promote_type(U1,U2)}
Base.@pure Base.promote_rule(::Type{FixedUInt{N1,U}}, ::Type{FixedUInt{N2,U}}) where {N1,N2,U<:BitUnsigned} = FixedUInt{max(N1,N2),U}

Base.convert(::Type{F}, a::F) where {F<:FixedUInt} = a
Base.convert(F::Type{<:FixedUInt}, a::Unsigned) = F(a)
Base.convert(F::Type{<:FixedUInt}, a::Signed) = F(convert(Unsigned, a))
function Base.convert(::Type{U}, a::FixedUInt{N, V}) where {U<:BitUnsigned, N, V<:BitUnsigned}
    b = zero(U)
    x = a.parts
    shift = unsigned(0)
    for k = 1:N
        db = convert(U, x[k])
        leading_zeros(db) < shift && throw(InexactError())
        b += (db << shift)
        shift += fullshift(V)
    end
    return b
end
function Base.convert(::Type{BigInt}, a::FixedUInt{N, V}) where {N, V<:BitUnsigned}
    b = zero(BigInt)
    x = a.parts
    shift = unsigned(0)
    for k = 1:N
        db = convert(BigInt, x[k])
        b += (db << shift)
        shift += fullshift(V)
    end
    return b
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
function Base.divrem(n::F, d::F) where {F<:FixedUInt}
    q, r = _tdivrem(n.parts, d.parts)
    return F(q), F(r)
end

## FlexibleUInt
##===============
struct FlexibleUInt{U<:BitUnsigned} <: Unsigned
    parts::Vector{U}
end
function FlexibleUInt{U}(a::BitUnsigned) where {U<:BitUnsigned}
    x = U[]
    while !iszero(a)
        push!(x, convert(U, a & typemax(U)))
        a >>= fullshift(U)
    end
    return FlexibleUInt{U}(x)
end
FlexibleUInt{U}(a::FlexibleUInt{U}) where {U<:BitUnsigned} = a
function Base.show(io::IO, a::FlexibleUInt)
    print(io,"0x")
    for k = length(a.parts):-1:1
        print(io, " ", repr(a.parts[k])[3:end])
    end
end

Base.promote_rule(F::Type{<:FlexibleUInt}, ::Type{<:Signed}) = F
Base.promote_rule(F::Type{<:FlexibleUInt}, ::Type{<:BitUnsigned}) = F
Base.promote_rule(::Type{FlexibleUInt{U1}}, ::Type{FlexibleUInt{U2}}) where {U1<:BitUnsigned,U2<:BitUnsigned} = FlexibleUInt{promote_type(U1,U2)}

Base.convert(::Type{F}, a::F) where {F<:FlexibleUInt} = a
Base.convert(F::Type{<:FlexibleUInt}, a::Unsigned) = F(a)
Base.convert(F::Type{<:FlexibleUInt}, a::Signed) = F(convert(Unsigned, a))
function Base.convert(::Type{U}, a::FlexibleUInt{V}) where {U<:BitUnsigned, V<:BitUnsigned}
    b = zero(U)
    x = a.parts
    shift = unsigned(0)
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

function Base.trailing_zeros(a::FlexibleUInt)
    isempty(a.parts) && return InexactError() # behavior of BigInt
    numzeros = 0
    k = 1
    @inbounds while iszero(a.parts[k])
        numzeros += trailing_zeros(a.parts[k])
        k += 1
    end
    numzeros += trailing_zeros(a.parts[k])
end


# arithmitic
Base.:+(a1::F, a2::F) where {F<:FlexibleUInt} =
    length(a1.parts) > length(a2.parts) ? F(_vadd!(copy(a1.parts), a2.parts)) :
                                        F(_vadd!(copy(a2.parts), a1.parts))
Base.:-(a1::F, a2::F) where {F<:FlexibleUInt} =
    a2 <= a1 ? F(_vsub!(copy(a1.parts), a2.parts)) : throw(OverflowError())
Base.:*(a1::F, a2::F) where {U<:BitUnsigned,F<:FlexibleUInt{U}} =
    F(_vmuladd!(fill(zero(U), length(a1.parts)+length(a2.parts)), a1.parts, a2.parts))
Base.divrem(n::F, d::F) where {F<:FlexibleUInt} = map(F, _vdivrem!(copy(n.parts), d.parts))
Base.div(n::F, d::F) where {F<:FlexibleUInt} = divrem(n, d)[1]
Base.rem(n::F, d::F) where {F<:FlexibleUInt} = divrem(n, d)[2]
Base.checked_abs(a::FlexibleUInt) = a

function Base.factorial(a::FlexibleUInt{U}) where {U<:BitUnsigned}
    b = copy(a.parts)
    u = [one(U)]
    f1 = copy(a.parts)
    f2 = Vector{U}()
    while true
        _vsub!(b, u)
        length(b) == 0 && break
        _vmuladd!(f2, f1, b)
        f1, f2 = f2, f1
        fill!(resize!(f2, length(f1)+length(b)), zero(U))
    end
    return FlexibleUInt{U}(f1)
end


end # module
