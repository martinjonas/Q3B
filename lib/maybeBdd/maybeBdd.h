#pragma once

#include <cuddObj.hh>
#include <optional>
#include <iostream>
#include <vector>

class MaybeBDD {
private:
    std::optional<BDD> innerBdd;
    static bool approximationHappened;

public:
MaybeBDD()
    {
	innerBdd = {};
    }

MaybeBDD(BDD bdd)
    : innerBdd(bdd)
    {

    }

    MaybeBDD& operator=(MaybeBDD other)
    {
	swap(other);
        return *this;
    }

    bool HasValue() const
    {
	return innerBdd.has_value();
    }

    BDD GetBDD() const
    {
	return innerBdd.value();
    }

    BDD GetBDD(BDD ifEmpty) const
    {
	if (!innerBdd.has_value())
	{
	    approximationHappened = true;
	}
	return innerBdd.value_or(ifEmpty);
    }

    MaybeBDD GetBDD(MaybeBDD ifEmpty) const
    {
	if (!innerBdd.has_value())
	{
	    approximationHappened = true;
            return ifEmpty;
	}
	return *this;
    }

    unsigned int NodeCount() const
    {
	if (innerBdd.has_value())
	{
	    return innerBdd.value().nodeCount();
	}

	return 0;
    }

    static void ResetApproximationFlag()
    {
	approximationHappened = false;
    }

    static bool ApproximationHappened()
    {
	return approximationHappened;
    }

    MaybeBDD And(const MaybeBDD&) const;
    MaybeBDD Or(const MaybeBDD&) const;
    MaybeBDD Xor(const MaybeBDD&) const;
    MaybeBDD Xnor(const MaybeBDD&) const;
    MaybeBDD Not() const;

    MaybeBDD Ite(const MaybeBDD&, const MaybeBDD&) const;

    bool IsOne() const
    {
	return HasValue() && GetBDD().IsOne();
    }

    bool IsZero() const
    {
	return HasValue() && GetBDD().IsZero();
    }

    bool IsVar() const
    {
	return !HasValue() || GetBDD().IsVar();
    }

    MaybeBDD operator&(const MaybeBDD& other) const
    {
	return this->And(other);
    }

    MaybeBDD operator&=(const MaybeBDD& other)
    {
	innerBdd = (*this & other).innerBdd;
	return *this;
    }

    MaybeBDD operator*(const MaybeBDD& other) const
    {
	return this->And(other);
    }

    MaybeBDD operator|(const MaybeBDD& other) const
    {
	return this->Or(other);
    }

    MaybeBDD operator|=(const MaybeBDD& other)
    {
	innerBdd = (*this | other).innerBdd;
	return *this;
    }

    MaybeBDD operator+(const MaybeBDD& other) const
    {
	return this->Or(other);
    }

    MaybeBDD operator!() const
    {
	return this->Not();
    }

    MaybeBDD operator~() const
    {
	return this->Not();
    }

    MaybeBDD operator^(const MaybeBDD& other) const
    {
	return this->Xor(other);
    }

    void swap(MaybeBDD& other)
    {
        using std::swap;
        swap(innerBdd, other.innerBdd);
    }

    bool Equals (const MaybeBDD& other) const
    {
	return (!this->HasValue() && !other.HasValue()) ||
	    (this->HasValue() && other.HasValue() && (this->GetBDD() == other.GetBDD()));
    }

    MaybeBDD LICompaction (BDD dontCare)
    {
	if (HasValue())
	{
	    return MaybeBDD(innerBdd.value().LICompaction(dontCare));
	}
	else
	{
	    return *this;
	}
    }

    MaybeBDD Minimize (BDD dontCare)
    {
	if (HasValue())
	{
	    return MaybeBDD(innerBdd.value().Minimize(dontCare));
	}
	else
	{
	    return *this;
	}
    }
};
