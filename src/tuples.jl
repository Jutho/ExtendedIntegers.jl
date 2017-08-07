using Base: front, tail, setindex

@inbounds begin
    _tfill(t::Tuple{}, x::Unsigned) = iszero(x) ? () : throw(InexactError)
    _tfill(t::NTuple{N,U}, x::Unsigned) where {N, U<:BitUnsigned} =
        (convert(U, x & typemax(U)), _tfill(tail(t), x >> fullshift(U))...)

    _tzero(t::Tuple{}) = ()
    _tzero(t::NTuple{N,U}) where {N, U<:BitUnsigned} = (zero(U), _tzero(tail(t))...)

    _tone(t::Tuple{}) = ()
    _tone(t::NTuple{N,U}) where {N, U<:BitUnsigned} = (one(U), _tzero(tail(t))...)

    _tcmp(t1::Tuple{}, t2::Tuple{}) = 0
    _tcmp(t1::NTuple{N,U}, t2::NTuple{N,U}) where {N, U<:BitUnsigned} =
        t1[N] == t2[N] ? _tcmp(front(t1), front(t2)) : cmp(t1[N], t2[N])


    _tfullleftshift(::Tuple{}) = ()
    _tfullleftshift(t::NTuple{N,U}) where {N, U<:BitUnsigned} = (zero(U), front(t)...)
    _tleftshift(::Tuple{}, n::Unsigned) = ()
    _tleftshift(::Tuple{}, n::Unsigned, carry::BitUnsigned) = ()
    function _tleftshift(t::NTuple{N,U}, n::Unsigned) where {N, U<:BitUnsigned}
        while n >= fullshift(U)
            t = _tfullleftshift(t)
            n -= fullshift(U)
        end
        n == 0 ? t : (t[1] << n, _tleftshift(tail(t), n, t[1] >> (fullshift(U)-n))...)
    end
    _tleftshift(t::NTuple{N,U}, n::Unsigned, carry::U) where {N, U<:BitUnsigned} =
        ((t[1] << n) | carry, _tleftshift(tail(t), n, t[1] >> (fullshift(U)-n))...)

    _tfullrightshift(::Tuple{}) = ()
    _tfullrightshift(t::NTuple{N,U}) where {N, U<:BitUnsigned} = (tail(t)..., zero(U))
    _trightshift(::Tuple{}, n::Unsigned) = ()
    _trightshift(::Tuple{}, n::Unsigned, carry::BitUnsigned) = ()
    function _trightshift(t::NTuple{N,U}, n::Unsigned) where {N, U<:BitUnsigned}
        while n >= fullshift(U)
            t = _tfullrightshift(t)
            n -= fullshift(U)
        end
        n == 0 ? t : (_trightshift(front(t), n, t[N] << (fullshift(U)-n))..., t[N] >> n)
    end
    _trightshift(t::NTuple{N,U}, n::Unsigned, carry::U) where {N, U<:BitUnsigned} =
        (_trightshift(front(t), n, t[N] << (fullshift(U)-n))..., carry | (t[N] >> n))

    _tand(::Tuple{}, ::Tuple{}) = ()
    _tand(t1::NTuple{N,U}, t2::NTuple{N,U}) where {N, U<:BitUnsigned} =
        (t1[1] & t2[1], _tand(tail(t1), tail(t2))...)

    _tor(::Tuple{}, ::Tuple{}) = ()
    _tor(t1::NTuple{N,U}, t2::NTuple{N,U}) where {N, U<:BitUnsigned} =
        (t1[1] | t2[1], _tor(tail(t1), tail(t2))...)

    _tnot(::Tuple{}) = ()
    _tnot(t::Tuple{N,U}) where {N, U<:BitUnsigned} = (~t[1], _tnot(tail(t))...)

    _tadd(::Tuple{}, ::Tuple{}) = ()
    _tadd(::Tuple{}, ::Tuple{}, carry::BitUnsigned) = ()
    function _tadd(t1::NTuple{N,U}, t2::NTuple{N,U}, carry::U = zero(U)) where {N, U<:BitUnsigned}
        s, ncarry = _add(t1[1], t2[1])
        if iszero(carry)
            carry = ncarry
        elseif iszero(ncarry)
            s, carry = _add(s, carry)
        else
            s += carry # cannot overflow
            carry = ncarry
        end
        (s, _tadd(tail(t1), tail(t2), carry)...)
    end

    _tsub(::Tuple{}, ::Tuple{}) = ()
    _tsub(::Tuple{}, ::Tuple{}, borrow::BitUnsigned) = ()
    function _tsub(t1::NTuple{N,U}, t2::NTuple{N,U}, borrow::U = zero(U)) where {N, U<:BitUnsigned}
        s, nborrow = _sub(t1[1], t2[1])
        if iszero(borrow)
            borrow = nborrow
        elseif iszero(nborrow)
            s, borrow = _sub(s, borrow)
        else
            s -= borrow # cannot overflow
            borrow = nborrow
        end
        (s, _tsub(tail(t1), tail(t2), borrow)...)
    end

    _tmul(::Tuple{}, ::Tuple{}) = ()
    _tmul(::Tuple{}, a::U, carry::U = zero(U)) where {U<:BitUnsigned} = ()
    function _tmul(t::NTuple{N,U}, a::U, carry::U = zero(U)) where {N, U<:BitUnsigned}0
        t1, carry1 = _mul(t[1], a) # carry1 <= typemax - 2
        t1, carry2 = _add(t1, carry) # carry2 <= 1
        carry = carry1 + carry2 # cannot overflow
        (t1, _tmul(tail(t), a, carry)...)
    end
    function _tmul(t1::NTuple{N,U}, t2::NTuple{N,U}) where {N, U<:BitUnsigned}
        (all(iszero, t1) || all(iszero, t2)) && return _tzero(t1)
        _tadd(_tmul(t1, t2[1]), (zero(U), _tmul(front(t1), tail(t2))...))
    end

    function _tdivrem(num::NTuple{N,U}, den::U) where {N, U<:BitUnsigned}
        iszero(den) && throw(DivideError())
        if iszero(num[N])
            qa, ra = _tdivrem(front(num), den)
            return (qa..., zero(U)), (ra..., zero(U))
        elseif num[N] >= den
            qN, rN = divrem(num[N], den)
            qb, rb = _tdivrem2((front(num)..., rN), den)
            return (qb..., qN), (rb..., zero(U))
        else
            qc, rc = _tdivrem2(num, den)
            return (qc..., zero(U)), (rc..., zero(U))
        end
    end
    function _tdivrem2(num::NTuple{N,U}, den::U) where {N, U<:BitUnsigned}
        q, r = _divrem(num[N-1], num[N], den)
        tq, tr = _tdivrem2((front(front(num))..., r), den)
        return (tq..., q), (tr..., zero(U))
    end
    _tdivrem2(num::Tuple{U,U}, den::U) where {U<:BitUnsigned} = map(tuple, _divrem(num[1], num[2], den))

    _tdivrem(num::Tuple{}, den::Tuple{})  = (), ()
    function _tdivrem(num::NTuple{N,U}, den::NTuple{N,U}) where {N, U<:BitUnsigned}
        all(iszero, tail(den)) && return _tdivrem(num, den[1])
        c = _tcmp(num, den)
        c < 0 && return (_tzero(num), num)
        c == 0 && return (_tone(num), _tzero(num))

        n = N
        while iszero(den[n])
            n-=1
        end
        s = unsigned(leading_zeros(den[n]))
        v = _tleftshift(den, s)
        u = _tleftshift((num..., zero(U)), s)
        m = N+1
        while iszero(u[m])
            m-=1
        end
        if u[m] > v[n]
            m+=1
        end
        m = m - n - 1

        q = _tzero(v)
        for j = m:-1:0
            q̂ = _estimateq(u[j+n-1],u[j+n],u[j+n+1], v[n-1], v[n])
            vs = _tleftshift((v..., zero(U)), unsigned(j*fullshift(U)))
            p = _tmul(vs, q̂)
            if _tcmp(p, u) > 0
                q̂ -= one(q̂)
                p = _tsub(p, vs)
            end
            u = _tsub(u, p)
            q = Base.setindex(q, q̂, j+1)
        end
        r = _trightshift(front(u), s)
        return q, r
    end
end
