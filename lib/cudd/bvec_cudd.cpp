//
// Created by pnavratil on 7/7/17.
//

#include "bvec_cudd.h"
#include "../Solver.h"
#include <climits>
#include <iostream>

namespace cudd
{

Bvec::Bvec(Cudd &manager) : m_manager(&manager), m_bitvec(0) {}

Bvec::Bvec(Cudd &manager, size_t bitnum, const MaybeBDD &value)
    : m_manager(&manager), m_bitvec(bitnum, value)
{
}

Bvec::Bvec(Cudd &manager, size_t bitnum, const BDD &value)
    : m_manager(&manager), m_bitvec(bitnum, MaybeBDD(value))
{
}

Bvec::Bvec(const Bvec &other)
    : m_manager(other.m_manager), m_bitvec(other.m_bitvec)
{
}

Bvec &Bvec::operator=(Bvec other)
{
    swap(other);
    return *this;
}

void Bvec::set(size_t i, const BDD &con) { m_bitvec.at(i) = MaybeBDD(con); }

void Bvec::set(size_t i, const MaybeBDD &con) { m_bitvec.at(i) = con; }

MaybeBDD &Bvec::operator[](size_t i) { return m_bitvec.at(i); }

const MaybeBDD &Bvec::operator[](size_t i) const { return m_bitvec.at(i); }

size_t Bvec::bitnum() const { return m_bitvec.size(); }

Cudd &Bvec::manager() const { return *m_manager; }

bool Bvec::empty() const { return m_bitvec.empty(); }

Bvec Bvec::bvec_build(Cudd &manager, size_t bitnum, bool isTrue)
{
    Bvec res(manager, bitnum, isTrue ? manager.bddOne() : manager.bddZero());
    return res;
}

Bvec Bvec::bvec_true(Cudd &manager, size_t bitnum)
{
    return bvec_build(manager, bitnum, true);
}

Bvec Bvec::bvec_false(Cudd &manager, size_t bitnum)
{
    return bvec_build(manager, bitnum, false);
}

Bvec Bvec::bvec_con(Cudd &manager, size_t bitnum, unsigned int val)
{
    Bvec res = reserve(manager, bitnum);
    if (val < 0) {
        throw std::logic_error("use bvec_ncon for negative values");
    }
    for (size_t i = 0U; i < bitnum; ++i) {
        if (val & 1U) {
            res.m_bitvec.push_back(MaybeBDD(manager.bddOne()));
        } else {
            res.m_bitvec.push_back(MaybeBDD(manager.bddZero()));
        }
        val >>= 1U;
    }
    return res;
}

Bvec Bvec::bvec_var(Cudd &manager, size_t bitnum, int offset, int step)
{
    Bvec res = bvec_false(manager, bitnum);
    for (size_t i = 0U; i < bitnum; ++i) {
        res[i] = MaybeBDD(manager.bddVar(offset + i * step));
    }

    return res;
}

Bvec Bvec::bvec_coerce(size_t bits) const
{
    Bvec res = bvec_false(*m_manager, bits);
    size_t minnum = std::min(bits, bitnum());
    for (size_t i = 0U; i < minnum; ++i) {
        res[i] = m_bitvec[i];
    }
    return res;
}

Bvec Bvec::arithmetic_neg(const Bvec &src)
{
    return ~src + bvec_con(src.manager(), src.bitnum(), 1);
}

bool Bvec::bvec_isConst() const
{
    for (size_t i = 0U; i < bitnum(); ++i) {
        if (!(m_bitvec[i].IsOne() || m_bitvec[i].IsZero())) {
            return false;
        }
    }
    return true;
}

unsigned int Bvec::bvec_varBits() const
{
    unsigned int varBits = 0;
    for (size_t i = 0U; i < bitnum(); ++i) {
        if (m_bitvec[i].IsOne() || m_bitvec[i].IsZero()) {
            varBits++;
        }
    }
    return varBits;
}

int Bvec::bvec_val() const
{
    int val = 0;
    for (size_t i = bitnum(); i >= 1U; --i) {
        if (m_bitvec[i - 1U].IsOne())
            val = (val << 1) | 1;
        else if (m_bitvec[i - 1U].IsZero())
            val = val << 1;
        else
            return 0;
    }
    return val;
}

Bvec Bvec::bvec_copy(const Bvec &other) { return Bvec(other); }

Bvec Bvec::bvec_map1(const Bvec &src,
                     std::function<MaybeBDD(const MaybeBDD &)> fun)
{
    Bvec res = reserve(*src.m_manager, src.bitnum());
    for (size_t i = 0; i < src.bitnum(); ++i) {
        res.m_bitvec.push_back(fun(src[i]));
    }
    return res;
}

Bvec Bvec::bvec_map2(
    const Bvec &first, const Bvec &second,
    std::function<MaybeBDD(const MaybeBDD &, const MaybeBDD &)> fun)
{
    Cudd &manager = check_same_cudd(*first.m_manager, *second.m_manager);
    Bvec res(manager);

    if (first.bitnum() != second.bitnum()) {
        return res;
    }

    reserve(res, first.bitnum());
    for (size_t i = 0U; i < first.bitnum(); ++i) {
        res.m_bitvec.push_back(fun(first[i], second[i]));
    }
    return res;
}

Bvec Bvec::bvec_add(const Bvec &left, const Bvec &right)
{
    return bvec_add_nodeLimit(left, right, UINT_MAX);
}

Bvec Bvec::bvec_add_nodeLimit(const Bvec &left, const Bvec &right,
                              unsigned int nodeLimit)
{
    Cudd &manager = check_same_cudd(*left.m_manager, *right.m_manager);
    Bvec res(manager);
    MaybeBDD comp(manager.bddZero());

    if (left.bitnum() == 0 || right.bitnum() == 0 ||
        left.bitnum() != right.bitnum()) {
        return res;
    }

    if (left.supportSize() > right.supportSize()) {
        return bvec_add_nodeLimit(right, left, nodeLimit);
    }

    reserve(res, left.bitnum());

    unsigned int preciseBdds = 0;
    for (size_t i = 0U; i < left.bitnum(); ++i) {

        res.m_bitvec.push_back((left[i] ^ right[i]) ^ comp);

        preciseBdds++;
        if (nodeLimit != UINT_MAX && res.bddNodes() > nodeLimit) {
            break;
        }

        comp = (left[i] & right[i]) | (comp & (left[i] | right[i]));
    }

    for (size_t i = (size_t)preciseBdds; i < left.bitnum(); i++) {
        res.m_bitvec.push_back(MaybeBDD{});
    }

    return res;
}

Bvec Bvec::bvec_sub(const Bvec &left, const Bvec &right)
{
    Cudd &manager = check_same_cudd(*left.m_manager, *right.m_manager);
    Bvec res(manager);
    MaybeBDD comp(manager.bddZero());

    if (left.bitnum() == 0 || right.bitnum() == 0 ||
        left.bitnum() != right.bitnum()) {
        return res;
    }

    reserve(res, left.bitnum());

    for (size_t i = 0U; i < left.bitnum(); ++i) {

        /* bitvec[n] = l[n] ^ r[n] ^ comp; */
        res.m_bitvec.push_back((left[i] ^ right[i]) ^ comp);
        /* comp = (l[n] & r[n] & comp) | (!l[n] & (r[n] | comp)); */
        comp = (left[i] & right[i] & comp) | (~left[i] & (right[i] | comp));
    }

    return res;
}

Bvec Bvec::bvec_mulfixed(int con) const
{
    Bvec res(*m_manager);

    if (bitnum() == 0) {
        return res;
    }

    if (con == 0) {
        return bvec_false(*m_manager,
                          bitnum()); /* return false array (base case) */
    }

    Bvec next = bvec_false(*m_manager, bitnum());
    for (size_t i = 1U; i < bitnum(); ++i) {
        next[i] = m_bitvec[i - 1];
    }

    Bvec rest = next.bvec_mulfixed(con >> 1);

    if (con & 0x1) {
        res = bvec_add(*this, rest);
    } else {
        res = rest;
    }

    return res;
}

Bvec Bvec::bvec_mul(const Bvec &left, const Bvec &right)
{
    return bvec_mul_nodeLimit(left, right, UINT_MAX);
}

Bvec Bvec::bvec_mul_nodeLimit(const Bvec &left, const Bvec &right,
                              unsigned int nodeLimit)
{
    size_t bitnum = std::max(left.bitnum(), right.bitnum());
    Cudd &manager = check_same_cudd(*left.m_manager, *right.m_manager);
    Bvec res = bvec_false(manager, bitnum);

    if (left.bitnum() == 0 || right.bitnum() == 0) {
        return res;
    }
    Bvec leftshifttmp = Bvec(left);
    Bvec leftshift = leftshifttmp.bvec_coerce(bitnum);

    if (left.supportSize() > right.supportSize()) {
        return bvec_mul_nodeLimit(right, left, nodeLimit);
    }

    unsigned int preciseBdds = 0;
    for (size_t i = 0U; i < right.bitnum(); ++i) {
        if (right[i].IsZero()) {
            preciseBdds++;
        } else {
            Bvec added = bvec_add(res, leftshift);

            bool tooManyNodes = false;
            for (size_t m = 0U; m < right.bitnum(); ++m) {

                res[m] = right[i].Ite(added[m], res[m]);

                if (nodeLimit != UINT_MAX && res[m].NodeCount() > nodeLimit) {
                    tooManyNodes = true;

                    if (m >= preciseBdds) {
                        preciseBdds++;
                    }

                    break;
                }
            }

            if (tooManyNodes) {
                break;
            } else {
                preciseBdds++;
            }
        }

        /* Shift 'leftshift' one bit left */
        for (size_t m = bitnum - 1U; m >= 1U; --m) {
            leftshift[m] = leftshift[m - 1];
        }

        leftshift[0] = MaybeBDD(manager.bddZero());
    }

    for (size_t m = preciseBdds; m < bitnum; ++m) {
        res[m] = MaybeBDD{};
    }

    return res;
}

void Bvec::bvec_div_rec(Bvec &divisor, Bvec &remainder, Bvec &result,
                        size_t step)
{
    Cudd &manager = *result.m_manager;
    MaybeBDD isSmaller = bvec_lte(divisor, remainder);
    Bvec newResult = result.bvec_shlfixed(1, isSmaller);
    Bvec zero = bvec_build(manager, divisor.bitnum(), false);
    Bvec sub = reserve(manager, divisor.bitnum());

    for (size_t i = 0U; i < divisor.bitnum(); ++i) {
        sub.m_bitvec.push_back(isSmaller.Ite(divisor[i], zero[i]));
    }

    Bvec tmp = remainder - sub;
    Bvec newRemainder = tmp.bvec_shlfixed(1, result[divisor.bitnum() - 1]);

    if (step > 1) {
        bvec_div_rec(divisor, newRemainder, newResult, step - 1);
    }

    result = newResult;
    remainder = newRemainder;
}

int Bvec::bvec_divfixed(size_t con, Bvec &result, Bvec &rem) const
{
    if (con > 0) {
        Bvec divisor = bvec_con(*m_manager, bitnum(), con);
        Bvec tmp = bvec_false(*m_manager, bitnum());
        Bvec tmpremainder = tmp.bvec_shlfixed(1, m_bitvec[bitnum() - 1]);
        Bvec res = bvec_shlfixed(1, MaybeBDD(m_manager->bddZero()));

        bvec_div_rec(divisor, tmpremainder, res, divisor.bitnum());
        Bvec remainder =
            tmpremainder.bvec_shrfixed(1, MaybeBDD(m_manager->bddZero()));

        result = res;
        rem = remainder;
        return 0;
    }
    return 1;
}

int Bvec::bvec_div(const Bvec &left, const Bvec &right, Bvec &result,
                   Bvec &remainder)
{
    return bvec_div_nodeLimit(left, right, result, remainder, UINT_MAX);
}

int Bvec::bvec_div_nodeLimit(const Bvec &left, const Bvec &right, Bvec &result,
                             Bvec &remainder, unsigned int nodeLimit)
{
    size_t bitnum = left.bitnum() + right.bitnum();
    Cudd &manager = check_same_cudd(*left.m_manager, *right.m_manager);
    if (left.bitnum() == 0 || right.bitnum() == 0 ||
        left.bitnum() != right.bitnum()) {
        return 1;
    }

    Bvec rem = left.bvec_coerce(bitnum);
    Bvec divtmp = right.bvec_coerce(bitnum);
    Bvec div = divtmp.bvec_shlfixed(left.bitnum(), MaybeBDD(manager.bddZero()));

    Bvec res = bvec_false(manager, right.bitnum());

    unsigned int preciseBdds = 0;
    for (size_t i = 0U; i < right.bitnum() + 1; ++i) {
        MaybeBDD divLteRem = bvec_lte(div, rem);
        Bvec remSubDiv = bvec_sub(rem, div);

        for (size_t j = 0U; j < bitnum; ++j) {
            rem[j] = divLteRem.Ite(remSubDiv[j], rem[j]);
        }

        if (i > 0) {
            res[right.bitnum() - i] = divLteRem;
        }

        preciseBdds++;
        if (nodeLimit != UINT_MAX &&
            (res.bddNodes() > nodeLimit || rem.bddNodes() > nodeLimit)) {
            break;
        }

        /* Shift 'div' one bit right */
        for (size_t j = 0U; j < bitnum - 1; ++j) {
            div[j] = div[j + 1];
        }

        div[bitnum - 1] = MaybeBDD(manager.bddZero());
    }

    // the first bit of the result was not stored
    if (preciseBdds > 0) {
        preciseBdds--;
    }

    // forget lower bits, as then can be imprecise
    for (unsigned int i = preciseBdds; i < right.bitnum(); i++) {
        res[right.bitnum() - i - 1] = MaybeBDD{};
    }

    if (preciseBdds != right.bitnum()) {
        for (unsigned int i = 0; i < right.bitnum(); i++) {
            rem[i] = MaybeBDD{};
        }
    }

    result = res;
    remainder = rem.bvec_coerce(right.bitnum());
    return 0;
}

Bvec Bvec::bvec_ite(const MaybeBDD &val, const Bvec &left, const Bvec &right)
{
    return bvec_ite_nodeLimit(val, left, right, UINT_MAX);
}

Bvec Bvec::bvec_ite_nodeLimit(const MaybeBDD &val, const Bvec &left,
                              const Bvec &right, unsigned int nodeLimit)
{
    Cudd &manager = check_same_cudd(*left.m_manager, *right.m_manager);
    Bvec res(manager);

    if (left.bitnum() != right.bitnum()) {
        return res;
    }
    reserve(res, left.bitnum());

    auto preciseBdds = 0U;
    if (nodeLimit != 0) {
        for (size_t i = 0U; i < left.bitnum(); ++i) {
            res.m_bitvec.push_back(val.Ite(left[i], right[i]));

            preciseBdds++;

            if (nodeLimit != UINT_MAX && res.bddNodes() > nodeLimit) {
                break;
            }
        }
    }

    for (size_t i = preciseBdds; i < left.bitnum(); ++i) {
        res.m_bitvec.push_back(MaybeBDD{});
    }
    return res;
}

Bvec Bvec::bvec_shlfixed(unsigned int pos, const MaybeBDD &con) const
{

    size_t min = (bitnum() < pos) ? bitnum() : pos;

    if (pos < 0U || bitnum() == 0) {
        return Bvec(*m_manager);
    }

    Bvec res(*m_manager, bitnum(), con);
    for (size_t i = min; i < bitnum(); i++) {
        res[i] = m_bitvec[i - pos];
    }
    return res;
}

Bvec Bvec::bvec_shl(const Bvec &left, const Bvec &right, const MaybeBDD &con)
{
    Cudd &manager = check_same_cudd(*left.m_manager, *right.m_manager);
    Bvec res(manager);
    if (left.bitnum() == 0 || right.bitnum() == 0) {

        return res;
    }

    res = bvec_false(manager, left.bitnum());

    for (size_t i = 0U; i <= left.bitnum(); ++i) {
        Bvec val = bvec_con(manager, right.bitnum(), i);
        MaybeBDD rEquN = bvec_equ(right, val);

        for (size_t j = 0U; j < left.bitnum(); ++j) {
            /* Set the m'th new location to be the (m+n)'th old location */
            if (j >= i) {
                res[j] |= rEquN & left[j - i];
            } else {
                res[j] |= rEquN & con;
            }
        }
    }

    /* At last make sure 'c' is shifted in for r-values > l-bitnum */
    Bvec val = bvec_con(manager, right.bitnum(), left.bitnum());
    MaybeBDD rEquN = bvec_gth(right, val);

    for (size_t i = 0U; i < left.bitnum(); i++) {
        res[i] |= (rEquN & con);
    }

    return res;
}

Bvec Bvec::bvec_shrfixed(unsigned int pos, const MaybeBDD &con) const
{
    if (pos < 0 || bitnum() == 0) {
        return Bvec(*m_manager);
    }
    unsigned int maxnum =
        std::max(static_cast<unsigned int>(bitnum()) - pos, 0U);
    Bvec res(*m_manager, bitnum(), con);

    for (size_t i = 0U; i < maxnum; ++i) {
        res[i] = m_bitvec[i + pos];
    }
    return res;
}

Bvec Bvec::bvec_shr(const Bvec &left, const Bvec &right, const MaybeBDD &con)
{
    Cudd &manager = check_same_cudd(*left.m_manager, *right.m_manager);
    Bvec res(manager);
    if (left.bitnum() == 0 || right.bitnum() == 0) {
        return res;
    }

    res = bvec_false(manager, left.bitnum());
    MaybeBDD tmp1, rEquN;

    for (size_t i = 0U; i <= left.bitnum(); ++i) {
        Bvec val = bvec_con(manager, right.bitnum(), i);
        rEquN = right == val;

        for (size_t j = 0U; j < left.bitnum(); ++j) {
            /* Set the m'th new location to be the (m+n)'th old location */
            if (j + i < left.bitnum())
                tmp1 = rEquN & left[j + i];
            else
                tmp1 = rEquN & con;
            res[j] = res[j] | tmp1;
        }
    }

    /* At last make sure 'c' is shifted in for r-values > l-bitnum */
    Bvec val = bvec_con(manager, right.bitnum(), left.bitnum());
    rEquN = bvec_gth(right, val);
    tmp1 = rEquN & con;

    for (size_t i = 0U; i < left.bitnum(); ++i) {
        res[i] = res[i] | tmp1;
    }
    return res;
}

MaybeBDD Bvec::bvec_lth(const Bvec &left, const Bvec &right)
{
    return bvec_lth_approx(left, right, MaybeBDD{});
}

BDD Bvec::bvec_lth_overApprox(const Bvec &left, const Bvec &right)
{
    return bvec_lth_approx(left, right, left.m_manager->bddOne());
}

BDD Bvec::bvec_lth_underApprox(const Bvec &left, const Bvec &right)
{
    return bvec_lth_approx(left, right, left.m_manager->bddZero());
}

MaybeBDD Bvec::bvec_lte(const Bvec &left, const Bvec &right)
{
    return bvec_lte_approx(left, right, MaybeBDD{});
}

BDD Bvec::bvec_lte_overApprox(const Bvec &left, const Bvec &right)
{
    return bvec_lte_approx(left, right, left.m_manager->bddOne());
}

BDD Bvec::bvec_lte_underApprox(const Bvec &left, const Bvec &right)
{
    return bvec_lte_approx(left, right, left.m_manager->bddZero());
}

MaybeBDD Bvec::bvec_gth(const Bvec &left, const Bvec &right)
{
    return bvec_lth(right, left);
}

MaybeBDD Bvec::bvec_gte(const Bvec &left, const Bvec &right)
{
    return !bvec_lte(right, left);
}

MaybeBDD Bvec::bvec_slth(const Bvec &left, const Bvec &right)
{
    return bvec_slth_approx(left, right, MaybeBDD{});
}

BDD Bvec::bvec_slth_overApprox(const Bvec &left, const Bvec &right)
{
    return bvec_slth_approx(left, right, left.m_manager->bddOne());
}

BDD Bvec::bvec_slth_underApprox(const Bvec &left, const Bvec &right)
{
    return bvec_slth_approx(left, right, left.m_manager->bddZero());
}

MaybeBDD Bvec::bvec_slte(const Bvec &left, const Bvec &right)
{
    return bvec_slte_approx(left, right, MaybeBDD{});
}

BDD Bvec::bvec_slte_overApprox(const Bvec &left, const Bvec &right)
{
    return bvec_slte_approx(left, right, left.m_manager->bddOne());
}

BDD Bvec::bvec_slte_underApprox(const Bvec &left, const Bvec &right)
{
    return bvec_slte_approx(left, right, left.m_manager->bddZero());
}

MaybeBDD Bvec::get_signs(const MaybeBDD &left, const MaybeBDD &right,
                         Cudd &manager)
{
    MaybeBDD differentSigns = left.Xnor(MaybeBDD(manager.bddOne())) &
                              right.Xnor(MaybeBDD(manager.bddZero()));
    return differentSigns;
}

MaybeBDD Bvec::bvec_sgth(const Bvec &left, const Bvec &right)
{
    return !bvec_slte(left, right);
}

MaybeBDD Bvec::bvec_sgte(const Bvec &left, const Bvec &right)
{
    return !bvec_slth(left, right);
}

MaybeBDD Bvec::bvec_equ(const Bvec &left, const Bvec &right)
{
    return bvec_equ_approx(left, right, MaybeBDD{});
}

BDD Bvec::bvec_equ_overApprox(const Bvec &left, const Bvec &right)
{
    return bvec_equ_approx(left, right, left.m_manager->bddOne());
}

BDD Bvec::bvec_equ_underApprox(const Bvec &left, const Bvec &right)
{
    return bvec_equ_approx(left, right, left.m_manager->bddZero());
}

MaybeBDD Bvec::bvec_nequ(const Bvec &left, const Bvec &right)
{
    return bvec_nequ_approx(left, right, MaybeBDD{});
}

BDD Bvec::bvec_nequ_overApprox(const Bvec &left, const Bvec &right)
{
    return bvec_nequ_approx(left, right, left.m_manager->bddOne());
}

BDD Bvec::bvec_nequ_underApprox(const Bvec &left, const Bvec &right)
{
    return bvec_nequ_approx(left, right, left.m_manager->bddZero());
}

Cudd &Bvec::check_same_cudd(Cudd &first, Cudd &second)
{
    DdManager *first_manager = first.getManager();
    DdManager *second_manager = second.getManager();
    if (first_manager == second_manager) {
        return first;
    } else {
        throw std::logic_error("not equal managers");
    }
}

MaybeBDD Bvec::bdd_and(const MaybeBDD &first, const MaybeBDD &second)
{
    return first & second;
}

MaybeBDD Bvec::bdd_xor(const MaybeBDD &first, const MaybeBDD &second)
{
    return first ^ second;
}

MaybeBDD Bvec::bdd_or(const MaybeBDD &first, const MaybeBDD &second)
{
    return first | second;
}

MaybeBDD Bvec::bdd_not(const MaybeBDD &src) { return !src; }

void Bvec::swap(Bvec &other)
{
    using std::swap;
    swap(m_manager, other.m_manager);
    swap(m_bitvec, other.m_bitvec);
}

Bvec Bvec::reserve(Cudd &manager, size_t bitnum)
{
    Bvec res(manager);
    res.m_bitvec.reserve(bitnum);
    return res;
}

void Bvec::reserve(Bvec &bitvector, size_t bitnum)
{
    bitvector.m_bitvec.reserve(bitnum);
}

} // namespace cudd
