module ExtendedIntegers

export FlexibleUInt

using Base.BitUnsigned, Base.BitUnsigned_types
using Base.front, Base.tail

for U in BitUnsigned_types
    @eval begin
        fullshift(::Type{$U}) = $(8*sizeof(U))
        halfshift(::Type{$U}) = $(4*sizeof(U))
        halfmax(::Type{$U}) = $(typemax(U) >> 4*sizeof(U))
    end
end

fullshift(a::BitUnsigned) = fullshift(typeof(a))
halfshift(a::BitUnsigned) = halfshift(typeof(a))
halfmax(a::BitUnsigned) = halfmax(typeof(a))
_split(a::BitUnsigned) = a & halfmax(a), a >> halfshift(a)

_add(a::U, b::U) where {U<:BitUnsigned} = a+b, U(a > ~b)
_sub(a::U, b::U) where {U<:BitUnsigned} = a-b, U(b > a)
function _mul(a::U, b::U) where {U<:BitUnsigned}
    a0, a1 = _split(a)
    b0, b1 = _split(b)

    c00 = a0 * b0
    c11 = a1 * b1

    c01 = a0 * b1
    c10 = a1 * b0

    d1 = c11 + (c01 >> halfshift(U)) + (c10 >> halfshift(U))
    c01 <<= halfshift(U)
    c10 <<= halfshift(U)
    d1 += (c00 > ~c01)
    d0 = c00+c01
    d1 += (d0 > ~c10)
    d0 += c10

    return d0, d1
end

_divrem(n::U, d::U) where {U<:Unsigned} = divrem(n, d)
# divrem for a two word integer n1n0, provided that q is one word, i.e. n1 < d
function _divrem(n0::U, n1::U, d::U) where {U<:Unsigned}
    n1 > d && throw(OverflowError()) # TODO: remove when checked that we never call it otherwise
    iszero(n1) && return divrem(n0,d)

    # by splitting, the problem becomes: m3m2m1m0 / d1d0 -> q1q0 and r1r0
    if leading_zeros(d) >= halfshift(U)
        # simple case d1 = 0, also m3 = 0 given the promise n1 = m3m2 < d = d1d0
        # reduces to short division m2m1m0 / d0 -> q1q0 and r0
        d0 = d
        m2 = n1
        m0, m1 = _split(n0)
        q1, r1 = divrem( (m2 << halfshift(U)) + m1, d0)
        q0, r0 = divrem( (r1 << halfshift(U)) + m0, d0)
        return (q1 << halfshift(U)) + q0, r0
    else
        # first normalize
        s = leading_zeros(d)
        d = d << s
        n1 = (n1 << s) + (n0 >> (fullshift(U)-s)) # no overflow since n1 < d
        n0 = (n0 << s)

        # now split
        d0, d1 = _split(d) # d1 will be properly normalized
        # m3, m2 = _split(n1)
        m0, m1 = _split(n0)
        b = one(U) << halfshift(U)

        q̂, r̂ = divrem(n1, d1)
        # q̂ - q <= 2 (because of normalization) and q <= b-1
        # therefore q̂ <= b+1 and we can compute q̂*d0 without overflow
        if q̂*d0 > b*r̂+m1
            q̂ = q̂-one(q̂)
            r̂ += d1
            # repeat test (at most once since q̂ - q <= 2)
            if r̂ < b && q̂*d0 > b*r̂+m1
                q̂ = q̂-one(q̂)
                r̂ += d1
            end
        end
        q1 = q̂ # should now be exact

        # compute m3m2m1 - q*d1d0
        # = m3m2*b + m1 - q*d1*b - q*d0
        # = r*b + m1 - q*d0 # r*b might overflow, therefore subtract from r the high part of q*d0
        t0, t1 = _split(q1*d0)
        n1 = (r̂-t1) << halfshift(U) + (m1-t0)

        # now we want n1*b+m0 / (d1*b+d0) -> q0, r0
        q̂, r̂ = divrem(n1, d1)
        if q̂*d0 > b*r̂+m0
            q̂ = q̂-one(q̂)
            r̂ += d1
            # repeat test (at most once since q̂ - q <= 2)
            if r̂ < b && q̂*d0 > b*r̂+m0
                q̂ = q̂-one(q̂)
                r̂ += d1
            end
        end
        q0 = q̂ # should now be exact

        t0, t1 = _split(q0*d0)
        r = (r̂-t1) << halfshift(U) + (m0-t0)
        q = q1 << halfshift(U) + q0
        return q, (r >> s)
    end
end

# alternative implementation using widening: works up to UInt64
function _mul2(a::U, b::U) where {U<:Union{UInt8,UInt16,UInt32,UInt64}}
    t = widen(a)*widen(b)
    c = convert(U, t & typemax(U))
    d = convert(U, (t >> fullshift(U)))
    return c, d
end
function _divrem2(n0::U, n1::U, d::U) where {U<:Union{UInt8,UInt16,UInt32,UInt64}}
    q, r = divrem((widen(n1)<<fullshift(U))+widen(n0), widen(d))
    return convert(U, q), convert(U, r)
end

### FixedWidthUInt
# struct FixedWidthUInt{N,U<:BitUnsigned} <: Unsigned
#     parts::NTuple{N,U}
# end


### FlexibleUInt
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

Base.iszero(a::FlexibleUInt) = length(a.parts) == 0
Base.zero(::Type{FlexibleUInt{U}}) where {U<:BitUnsigned} = FlexibleUInt{U}(U[])
Base.one(::Type{FlexibleUInt{U}}) where {U<:BitUnsigned} = FlexibleUInt{U}([one(U)])

Base.:<(a1::FlexibleUInt{U}, a2::FlexibleUInt{U}) where {U<:Unsigned} = _vcmp(a1.parts, a2.parts) < 0
Base.:<=(a1::FlexibleUInt{U}, a2::FlexibleUInt{U}) where {U<:Unsigned} = _vcmp(a1.parts, a2.parts) <= 0
Base.:(==)(a1::FlexibleUInt{U}, a2::FlexibleUInt{U}) where {U<:Unsigned} = a1.parts == a2.parts

Base.:<<(a::F, n::UInt) where {F<:FlexibleUInt} = F(_vleftshift!(copy(a.parts), n))
Base.:>>(a::F, n::UInt) where {F<:FlexibleUInt} = F(_vrightshift!(copy(a.parts), n))
Base.:>>>(a::FlexibleUInt, n::UInt) = >>(a, n)
Base.:&(a1::F, a2::F) where {F<:FlexibleUInt} =
    length(a1.parts) > length(a2.parts) ? F(_vand!(copy(a2.parts), a1.parts)) :
                                            F(_vand!(copy(a1.parts), a2.parts))
Base.:|(a1::F, a2::F) where {F<:FlexibleUInt} =
    length(a1.parts) > length(a2.parts) ? F(_vor!(copy(a1.parts), a2.parts)) :
                                            F(_vor!(copy(a2.parts), a1.parts))

Base.:+(a1::F, a2::F) where {F<:FlexibleUInt} =
    length(a1.parts) > length(a2.parts) ? F(_vadd!(copy(a1.parts), a2.parts)) :
                                        F(_vadd!(copy(a2.parts), a1.parts))
Base.:-(a1::F, a2::F) where {F<:FlexibleUInt} =
    a2 <= a1 ? F(_vsub!(copy(a1.parts), a2.parts)) : throw(OverflowError())
Base.:*(a1::F, a2::F) where {U,F<:FlexibleUInt{U}} =
    F(_vmuladd!(fill(zero(U), length(a1.parts)+length(a2.parts)), a1.parts, a2.parts))
Base.divrem(n::F, d::F) where {U,F<:FlexibleUInt{U}} = map(F, _vdivrem!(copy(n.parts), d.parts))

function _vcmp(x1::Vector{U}, x2::Vector{U}) where {U<:Unsigned}
    l1, l2 = length(x1), length(x2)
    if l2 == l1
        for k = l1:-1:1
            if x1[k] != x2[k]
                return cmp(x1[k], x2[k])
            end
        end
        return 0
    else
        return cmp(l1, l2)
    end
end

function _vleftshift!(x::Vector{U}, n::UInt) where {U<:BitUnsigned}
    n==0 && return x
    k = 1
    while n >= fullshift(U)
        n -= fullshift(U)
        unshift!(x, zero(U))
        k += 1
    end
    carry = zero(U)
    @inbounds while k <= length(x)
        # nextcarry = x[k] >> (fullshift(U)-n)
        # x[k] = (x[k] << n) + carry
        # carry = nextcarry
        carry, x[k] = (x[k] >> (fullshift(U)-n)) , ((x[k] << n) + carry)
        k += 1
    end
    !iszero(carry) && push!(x, carry)
    return x
end
function _vrightshift!(x::Vector{U}, n::UInt) where {U<:BitUnsigned}
    n==0 && return x
    k = 1
    while n >= fullshift(U) && length(x) > 0
        n -= fullshift(U)
        shift!(x)
    end
    length(x) == 0 && return x
    while k < length(x)
        x[k] = (x[k] >> n) | (x[k+1] << (fullshift(U)-n))
        k += 1
    end
    x[k] = (x[k] >> n)

    iszero(x[k]) && pop!(x)
    return x
end
function _vand!(y::Vector{U}, x::Vector{U}) where {U<:BitUnsigned}
    while length(y) > length(x)
        pop!(y)
    end
    @inbounds for k in 1:length(y)
        y[k] &= x[k]
    end
    while length(y) > 0 && iszero(last(y))
        pop!(y)
    end
    return y
end
function _vor!(y::Vector{U}, x::Vector{U}) where {U<:BitUnsigned}
    while length(y) < length(x)
        push!(y, zero(U))
    end
    @inbounds for k = 1:length(x)
        y[k] |= x[k]
    end
    return y
end

function _vadd!(y::Vector{U}, x::Vector{U}) where {U<:BitUnsigned}
    while length(y) < length(x)
        push!(y, zero(U))
    end
    lx, ly = length(x), length(y)
    carry = zero(U)
    for k = 1:lx
        y[k], ncarry = _add(y[k], x[k])
        if iszero(carry)
            carry = ncarry
        elseif iszero(ncarry)
            y[k], carry = _add(y[k], carry)
        else # if ncarry is nonzero, y[k] < typemax and ...
            y[k] += carry # ... this cannot overflow since carry = 1
            carry = ncarry
        end
    end
    for k = (lx+1):ly
        iszero(carry) && break
        y[k], carry = _add(y[k], carry)
    end
    !iszero(carry) && push!(y, carry)
    return y
end

function _vsub!(y::Vector{U}, x::Vector{U}) where {U<:BitUnsigned}
    _vcmp(y,x) < 0 && throw(OverflowError())
    lx, ly = length(x), length(y)
    borrow = zero(U)
    for k = 1:lx
        y[k], nborrow = _sub(y[k], x[k])
        if iszero(borrow)
            borrow = nborrow
        elseif iszero(nborrow)
            y[k], borrow = _sub(y[k], borrow)
        else # if nborrow is nonzero, y[k] > 0 and ...
            y[k] -= borrow # ... this cannot overflow since borrow = 1
            borrow = nborrow
        end
    end
    for k=(lx+1):ly
        iszero(borrow) && break
        y[k], borrow = _sub(y[k], borrow)
    end
    while length(y) > 0 && iszero(last(y)) # remove zero words at beginning
        pop!(y)
    end
    return y
end
function _vmuladd!(y::Vector{U}, x1::Vector{U}, x2::Vector{U}) where {U<:BitUnsigned}
    while length(y) < length(x1)+length(x2)
        push!(y, zero(U))
    end
    l1, l2 = length(x1), length(x2)
    for l = 1:l2
        # if !iszero(x2[l]) # not worthwhile according to Knuth
            carry = zero(U)
            for k = 1:l1
                prod, carry1 = _mul(x1[k], x2[l]) # carry1 < typemax - 1
                y[k+l-1], carry2 = _add(y[k+l-1], prod) # carry2 <= 1
                y[k+l-1], carry3 = _add(y[k+l-1], carry) # carry3 <= 1 - carry2
                carry = carry1 + carry2 + carry3 # this should not overflow
            end
            for k = (l1+l):(l1+l2)
                iszero(carry) && break
                y[k], carry = _add(y[k], carry)
            end
        # end
    end
    while iszero(last(y))
        pop!(y)
    end
    return y
end
function _vdivrem!(num::Vector{U}, den::U) where {U<:BitUnsigned} # n will be destroyed in the process
    iszero(den) && throw(DivideError())
    length(num) == 0 && return(num, num)
    length(num) == 1 && return divrem(num[1], den)

    last(num) >= den && push!(num, zero(U))
    q = Vector{U}(length(num)-1)
    k = length(q)
    while length(num) >= 2
        q[k], r = _divrem(num[end-1], num[end], den)
        pop!(num)
        num[end] = r
        k -= 1
    end
    iszero(last(num)) && pop!(num)
    return q, num
end

function _vdivrem!(num::Vector{U}, den::Vector{U}) where {U<:BitUnsigned} # n will be destroyed in the process
    isempty(den) && throw(DivideError())
    _vcmp(num,den) < 0 && return (Vector{U}(0), num)
    length(den) == 1 && return _vdivrem!(num, den[1])

    # we now know that length(den) >= 2, length(num) >= length(den)
    #normalize
    s = unsigned(leading_zeros(last(den)))
    u = _vleftshift!(num, s)
    v = _vleftshift!(den, s) # d is modified but will be restored at the end

    n = length(v)
    # compare v with first n words of u
    m = length(u) - n
    k = n
    while k > 0 && u[m+k] == v[k]
        k -= 1
    end
    if k > 0 && u[m+k] < v[k] # smaller, but u in total larger
        m -= 1
    else
        push!(u, zero(U))
    end
    # now m = length(u) - n -1
    q = fill(zero(U), m+1)

    for j = m:-1:0
        q̂ = _estimateq(u[j+n-1],u[j+n],u[j+n+1], v[n-1], v[n])
        borrow = zero(U)
        for k=1:n # combination of _vmul! and _vadd!
            u[k+j], borrow1 = _sub(u[k+j], borrow) # borrow1 <= 1
            p, borrow2 = _mul(v[k], q̂) # borrow2 <= typemax - 2
            u[k+j], borrow3 = _sub(u[k+j], p) # borrow3 <= 1 - borrow1
            borrow = borrow1 + borrow2 + borrow3 # cannot overflow
        end
        u[j+n+1], borrow = _sub(u[n+j+1], borrow)
        if !iszero(borrow) # should happen rarely according to Knuth
            q̂ -= one(q̂)
            carry = zero(U)
            for k=1:n # add back: see _vadd!
                u[k+j], ncarry = _add(u[k+j], v[k])
                if iszero(carry)
                    carry = ncarry
                elseif iszero(ncarry)
                    u[k+j], carry = _add(u[k+j], carry)
                else
                    u[k+j] += carry
                    carry = ncarry
                end
            end
            u[n+j+1], carry = _add(u[n+j+1], carry)
            # @assert borrow == carry
        end
        # @assert u[n+j+1] == zero(u[n+j+1])
        q[j+1] = q̂
    end
    while length(u) > 0 && iszero(last(u))
        pop!(u)
    end
    # restore shift
    den = _vrightshift!(v, s) # d is modified but will be restored at the end
    r = _vrightshift!(u, s) # d is modified but will be restored at the end
    return q, r
end

# estimate single word divisor q from first tree words of dividend and first two
# words of divisor
function _estimateq(u′′, u′, u, v′, v)
    if v == u
        q̂ = typemax(u)
        r̂′, r̂ = _add(u′, v)
    else
        q̂, r̂′ = _divrem(u′, u, v)
        r̂ = zero(u)
    end
    p′, p = _mul(q̂, v′)
    if iszero(r̂) && (p > r̂′ || (p == r̂′ && p′ > u′′))
        q̂ -= one(q̂)
        r̂′, carry = _add(r̂′, v)
        r̂ += carry
        p′, borrow = _sub(p′, v′)
        p -= borrow
    end
    if iszero(r̂) && (p > r̂′ || (p == r̂′ && p′ > u′′))
        q̂ -= one(q̂)
    end
    return q̂
end

end # module
