#pragma once

#include <functional>

enum Precision { APPROXIMATED, PRECISE };

Precision operator && (const Precision &l, const Precision &r);

template <typename T>
struct Approximated
{
    T value;
    Precision isPrecise;

    template <typename TRes>
    Approximated<TRes> Apply(const std::function<TRes(T)> &f)
    {
	return {f(value), isPrecise};
    }

    template <typename TRes>
    Approximated<TRes> Apply2(const Approximated<T> &r, const std::function<TRes(T, T)> &f)
    {
	TRes res = f(value, r.value);
	return {res, isPrecise && r.isPrecise};
    }
};
