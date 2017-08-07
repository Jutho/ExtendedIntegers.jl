@inbounds begin
function _vcmp(x1::Vector{U}, x2::Vector{U}) where {U<:BitUnsigned}
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
    isempty(den) && throw(diverr)
    c = _vcmp(num,den)
    c < 0 && return (Vector{U}(0), num)
    c == 0 && return ([one(U)], Vector{U}(0))
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
end
