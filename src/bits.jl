using Base.BitUnsigned_types

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
