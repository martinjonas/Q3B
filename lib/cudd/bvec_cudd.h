#ifndef BDD_BVEC_H
#define BDD_BVEC_H

#include "../maybeBdd/maybeBdd.h"
#include <algorithm>
#include <cuddObj.hh>
#include <fstream>
#include <functional>
#include <set>
#include <vector>

namespace cudd
{

class Bvec
{
    Cudd *m_manager;

public:
    std::vector<MaybeBDD> m_bitvec;

    Bvec() = delete;

    Bvec(Cudd &manager);

    Bvec(Cudd &manager, size_t bitnum, const BDD &value);

    Bvec(Cudd &manager, size_t bitnum, const MaybeBDD &value);

    Bvec(const Bvec &other);

    Bvec &operator=(Bvec other);

    ~Bvec() = default;

    void set(size_t i, const BDD &con);

    void set(size_t i, const MaybeBDD &con);

    MaybeBDD &operator[](size_t i);

    const MaybeBDD &operator[](size_t i) const;

    size_t bitnum() const;

    Cudd &manager() const;

    bool empty() const;

    static Bvec bvec_build(Cudd &manager, size_t bitnum, bool isTrue);

    static Bvec bvec_true(Cudd &manager, size_t bitnum);

    static Bvec bvec_false(Cudd &manager, size_t bitnum);

    static Bvec bvec_con(Cudd &manager, size_t bitnum, unsigned int val);

    static Bvec bvec_var(Cudd &manager, size_t bitnum, int offset, int step);

    Bvec bvec_coerce(size_t bitnum) const;

    static Bvec arithmetic_neg(const Bvec &src);

    bool bvec_isConst() const;

    unsigned int bvec_varBits() const;

    int bvec_val() const;

    static Bvec bvec_copy(const Bvec &other);

    static Bvec bvec_map1(const Bvec &src,
                          std::function<MaybeBDD(const MaybeBDD &)> fun);

    static Bvec
    bvec_map2(const Bvec &first, const Bvec &second,
              std::function<MaybeBDD(const MaybeBDD &, const MaybeBDD &)> fun);

    static Bvec bvec_add(const Bvec &left, const Bvec &right);

    static Bvec bvec_add_nodeLimit(const Bvec &left, const Bvec &right,
                                   unsigned int);

    static Bvec bvec_sub(const Bvec &left, const Bvec &right);

    Bvec bvec_mulfixed(int con) const;

    static Bvec bvec_mul(const Bvec &left, const Bvec &right);

    static Bvec bvec_mul_nodeLimit(const Bvec &left, const Bvec &right,
                                   unsigned int);

    int bvec_divfixed(size_t con, Bvec &result, Bvec &rem) const;

    static int bvec_div(const Bvec &left, const Bvec &right, Bvec &result,
                        Bvec &rem);

    static int bvec_div_nodeLimit(const Bvec &left, const Bvec &right,
                                  Bvec &result, Bvec &rem, unsigned int);

    static Bvec bvec_ite(const MaybeBDD &val, const Bvec &left,
                         const Bvec &right);

    static Bvec bvec_ite_nodeLimit(const MaybeBDD &val, const Bvec &left,
                                   const Bvec &right, unsigned int);

    Bvec bvec_shlfixed(unsigned int pos, const MaybeBDD &con) const;

    static Bvec bvec_shl(const Bvec &left, const Bvec &right,
                         const MaybeBDD &con);

    Bvec bvec_shrfixed(unsigned int pos, const MaybeBDD &con) const;

    static Bvec bvec_shr(const Bvec &left, const Bvec &right,
                         const MaybeBDD &con);

    static MaybeBDD bvec_lth(const Bvec &left, const Bvec &right);

    template <typename TRet>
    static TRet bvec_lth_approx(const Bvec &left, const Bvec &right,
                                const TRet &defaultValue)
    {
        Cudd &manager = check_same_cudd(*left.m_manager, *right.m_manager);
        TRet p = manager.bddZero();

        if (left.bitnum() == 0 || right.bitnum() == 0 ||
            left.bitnum() != right.bitnum()) {
            return p;
        }

        for (size_t i = 0U; i < left.bitnum(); ++i) {
            p = ((!left[i]) & right[i]).GetBDD(defaultValue) |
                (left[i].Xnor(right[i]).GetBDD(defaultValue) & p);
        }

        return p;
    }

    static BDD bvec_lth_overApprox(const Bvec &left, const Bvec &right);

    static BDD bvec_lth_underApprox(const Bvec &left, const Bvec &right);

    static MaybeBDD bvec_lte(const Bvec &left, const Bvec &right);

    template <typename TRet>
    static TRet bvec_lte_approx(const Bvec &left, const Bvec &right,
                                const TRet &defaultValue)
    {
        Cudd &manager = check_same_cudd(*left.m_manager, *right.m_manager);
        TRet p = manager.bddOne();

        if (left.bitnum() == 0 || right.bitnum() == 0 ||
            left.bitnum() != right.bitnum()) {
            return p;
        }

        for (size_t i = 0U; i < left.bitnum(); ++i) {
            p = ((!left[i]) & right[i]).GetBDD(defaultValue) |
                (left[i].Xnor(right[i]).GetBDD(defaultValue) & p);
        }

        return p;
    }

    static BDD bvec_lte_overApprox(const Bvec &left, const Bvec &right);

    static BDD bvec_lte_underApprox(const Bvec &left, const Bvec &right);

    static MaybeBDD bvec_gth(const Bvec &left, const Bvec &right);

    static MaybeBDD bvec_gte(const Bvec &left, const Bvec &right);

    static MaybeBDD bvec_slth(const Bvec &left, const Bvec &right);

    template <typename TRet>
    static TRet bvec_slth_approx(const Bvec &left, const Bvec &right,
                                 const TRet &defaultValue)
    {
        Cudd &manager = check_same_cudd(*left.m_manager, *right.m_manager);

        if (left.bitnum() == 0 || right.bitnum() == 0) {
            return manager.bddZero();
        }

        size_t size = left.bitnum() - 1;

        auto differentSigns =
            get_signs(left[size], right[size], manager).GetBDD(defaultValue);
        if (differentSigns.IsOne()) {
            // negative < positive
            return differentSigns;
        } else if (left[size].IsZero() && right[size].IsOne()) {
            // positive < negative
            return manager.bddZero();
        } else {
            return differentSigns |
                   (left[size].Xnor(right[size]).GetBDD(defaultValue) &
                    bvec_lth_approx(left.bvec_coerce(size),
                                    right.bvec_coerce(size), defaultValue));
        }
    }

    static BDD bvec_slth_overApprox(const Bvec &left, const Bvec &right);

    static BDD bvec_slth_underApprox(const Bvec &left, const Bvec &right);

    static MaybeBDD bvec_slte(const Bvec &left, const Bvec &right);

    template <typename TRet>
    static TRet bvec_slte_approx(const Bvec &left, const Bvec &right,
                                 const TRet &defaultValue)
    {
        Cudd &manager = check_same_cudd(*left.m_manager, *right.m_manager);
        if (left.bitnum() == 0 || right.bitnum() == 0) {
            return manager.bddZero();
        }

        size_t size = left.bitnum() - 1;

        auto differentSigns =
            get_signs(left[size], right[size], manager).GetBDD(defaultValue);
        if (differentSigns.IsOne()) {
            // negative <= positive
            return differentSigns;
        } else if (left[size].IsZero() && right[size].IsOne()) {
            // positive <= negative
            return manager.bddZero();
        } else {
            return differentSigns |
                   (left[size].Xnor(right[size]).GetBDD(defaultValue) &
                    bvec_lte_approx(left.bvec_coerce(size),
                                    right.bvec_coerce(size), defaultValue));
        }
    }

    static BDD bvec_slte_overApprox(const Bvec &left, const Bvec &right);

    static BDD bvec_slte_underApprox(const Bvec &left, const Bvec &right);

    static MaybeBDD bvec_sgth(const Bvec &left, const Bvec &right);

    static MaybeBDD bvec_sgte(const Bvec &left, const Bvec &right);

    static MaybeBDD bvec_equ(const Bvec &left, const Bvec &right);

    template <typename TRet>
    static TRet bvec_equ_approx(const Bvec &left, const Bvec &right,
                                const TRet &defaultValue)
    {
        Cudd &manager = check_same_cudd(*left.m_manager, *right.m_manager);
        TRet p = manager.bddOne();

        if (left.bitnum() == 0 || right.bitnum() == 0 ||
            left.bitnum() != right.bitnum()) {
            return manager.bddZero();
        }

        for (size_t i = 0U; i < left.bitnum(); ++i) {
            p = p & left[i].Xnor(right[i]).GetBDD(defaultValue);
            if (p.IsZero()) {
                return p;
            }
        }
        return p;
    }

    static BDD bvec_equ_overApprox(const Bvec &left, const Bvec &right);

    static BDD bvec_equ_underApprox(const Bvec &left, const Bvec &right);

    static MaybeBDD bvec_nequ(const Bvec &left, const Bvec &right);

    template <typename TRet>
    static TRet bvec_nequ_approx(const Bvec &left, const Bvec &right,
                                 const TRet &defaultValue)
    {
        Cudd &manager = check_same_cudd(*left.m_manager, *right.m_manager);
        TRet p = manager.bddZero();

        if (left.bitnum() == 0 || right.bitnum() == 0 ||
            left.bitnum() != right.bitnum()) {
            return manager.bddZero();
        }

        for (size_t i = 0U; i < left.bitnum(); ++i) {
            p = p | left[i].Xor(right[i]).GetBDD(defaultValue);
            if (p.IsOne()) {
                return p;
            }
        }
        return p;
    }

    static BDD bvec_nequ_overApprox(const Bvec &left, const Bvec &right);

    static BDD bvec_nequ_underApprox(const Bvec &left, const Bvec &right);

    Bvec operator&(const Bvec &other) const
    {
        return bvec_map2(*this, other, bdd_and);
    }

    Bvec operator^(const Bvec &other) const
    {
        return bvec_map2(*this, other, bdd_xor);
    }

    Bvec operator|(const Bvec &other) const
    {
        return bvec_map2(*this, other, bdd_or);
    }

    Bvec operator!(void) const { return bvec_map1(*this, bdd_not); }

    Bvec operator~(void) const { return bvec_map1(*this, bdd_not); }

    Bvec operator<<(int con) const
    {
        return bvec_shlfixed(con, MaybeBDD(m_manager->bddZero()));
    }

    Bvec operator<<(const Bvec &other) const
    {
        return bvec_shl(*this, other, MaybeBDD(m_manager->bddZero()));
    }

    Bvec operator>>(int con) const
    {
        return bvec_shrfixed(con, MaybeBDD(m_manager->bddZero()));
    }

    Bvec operator>>(const Bvec &other) const
    {
        return bvec_shr(*this, other, MaybeBDD(m_manager->bddZero()));
    }

    Bvec operator+(const Bvec &other) const { return bvec_add(*this, other); }

    Bvec operator+=(const Bvec &other)
    {
        *this = bvec_add(*this, other);
        return *this;
    }

    Bvec operator-(const Bvec &other) { return bvec_sub(*this, other); }

    Bvec operator-=(const Bvec &other)
    {
        *this = bvec_sub(*this, other);
        return *this;
    }

    Bvec operator*(int con) const { return bvec_mulfixed(con); }

    Bvec operator*=(int con)
    {
        this->bvec_mulfixed(con);
        return *this;
    }

    Bvec operator*(const Bvec &other) const { return bvec_mul(*this, other); }

    Bvec operator*=(const Bvec &other)
    {
        *this = bvec_mul(*this, other);
        return *this;
    }

    MaybeBDD operator<(const Bvec &other) const
    {
        return bvec_lth(*this, other);
    }

    MaybeBDD operator<=(const Bvec &other) const
    {
        return bvec_lte(*this, other);
    }

    MaybeBDD operator>(const Bvec &other) const
    {
        return bvec_gth(*this, other);
    }

    MaybeBDD operator>=(const Bvec &other) const
    {
        return bvec_gte(*this, other);
    }

    MaybeBDD operator==(const Bvec &other) const
    {
        return bvec_equ(*this, other);
    }

    MaybeBDD operator!=(const Bvec &other) const { return !(*this == other); }

    unsigned int bddNodes() const
    {
        auto count = 0U;

        for (const auto &bdd : m_bitvec) {
            count += bdd.NodeCount();
        }

        return count;
    }

    unsigned int supportSize() const
    {
        std::set<unsigned int> support;
        for (const auto &bdd : m_bitvec) {
            if (bdd.HasValue()) {
                const auto bdd_support = bdd.GetBDD().SupportIndices();
                std::copy(bdd_support.begin(), bdd_support.end(),
                          std::inserter(support, support.begin()));
            }
        }

        return support.size();
    }

    bool isPrecise() const
    {
        for (const auto &bdd : m_bitvec) {
            if (!bdd.HasValue()) {
                return false;
            }
        }

        return true;
    }

private:
    static Cudd &check_same_cudd(Cudd &first, Cudd &second);

    static void bvec_div_rec(Bvec &divisor, Bvec &remainder, Bvec &result,
                             size_t step);

    static MaybeBDD bdd_and(const MaybeBDD &first, const MaybeBDD &second);

    static MaybeBDD bdd_xor(const MaybeBDD &first, const MaybeBDD &second);

    static MaybeBDD bdd_or(const MaybeBDD &first, const MaybeBDD &second);

    static MaybeBDD bdd_not(const MaybeBDD &src);

    static MaybeBDD get_signs(const MaybeBDD &left, const MaybeBDD &right,
                              Cudd &manager);

    void swap(Bvec &other);

    static Bvec reserve(Cudd &manager, size_t bitnum);

    static void reserve(Bvec &bitvector, size_t bitnum);
};

} // namespace cudd

#endif // BDD_BVEC_H
