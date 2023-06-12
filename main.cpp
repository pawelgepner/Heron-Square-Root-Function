// Software algorithms for computing floating point square root
// and performance evaluation wrappers.

#include <chrono>
#include <functional>
#include <iomanip>
#include <iostream>
#include <algorithm>
#include <math.h>
#include "half.hpp"

using half = half_float::half;

using namespace std::chrono;

const long int iterationsCount = 1000000;

#define FENV_SUPPORT 1

#ifdef __GNUC__
#define predict_true(x) __builtin_expect(!!(x), 1)
#define predict_false(x) __builtin_expect(x, 0)
#else
#define predict_true(x) (x)
#define predict_false(x) (x)
#endif

union asunit_u
{
	float _f;
	uint32_t _i;
};
union asfloat_u
{
	uint32_t _i;
	float _f;
};
union asuint64_u
{
	double _f;
	uint64_t _i;
};
union asdouble_u
{
	uint64_t _i;
	double _f;
};

#define asuint(f) ((asunit_u){f})._i
#define asfloat(i) ((asfloat_u){i})._f
#define asuint64(f) ((asuint64_u){f})._i
#define asdouble(i) ((asdouble_u){i})._f

static inline uint32_t mul32(uint32_t a, uint32_t b)
{
	return (uint64_t)a * b >> 32;
}

/* returns a*b*2^-64 - e, with error 0 <= e < 3.  */
static inline uint64_t mul64(uint64_t a, uint64_t b)
{
	uint64_t ahi = a >> 32;
	uint64_t alo = a & 0xffffffff;
	uint64_t bhi = b >> 32;
	uint64_t blo = b & 0xffffffff;
	return ahi * bhi + (ahi * blo >> 32) + (alo * bhi >> 32);
}

float __math_invalidf(float x)
{
	return (x - x) / (x - x);
}

double __math_invalid(double x)
{
	return (x - x) / (x - x);
}

static inline double eval_as_double(double x)
{
	double y = x;
	return y;
}

const uint16_t __rsqrt_tab[128] = {
	0xb451,	0xb2f0,	0xb196,	0xb044,	0xaef9,	0xadb6,	0xac79,	0xab43,	0xaa14,	0xa8eb,	0xa7c8,
	0xa6aa,	0xa592,	0xa480,	0xa373,	0xa26b,	0xa168,	0xa06a,	0x9f70,	0x9e7b,	0x9d8a,	0x9c9d,
	0x9bb5,	0x9ad1,	0x99f0,	0x9913,	0x983a,	0x9765,	0x9693,	0x95c4,	0x94f8,	0x9430,	0x936b,
	0x92a9,	0x91ea,	0x912e,	0x9075,	0x8fbe,	0x8f0a,	0x8e59,	0x8daa,	0x8cfe,	0x8c54,	0x8bac,
	0x8b07,	0x8a64,	0x89c4,	0x8925,	0x8889,	0x87ee,	0x8756,	0x86c0,	0x862b,	0x8599,	0x8508,
	0x8479,	0x83ec,	0x8361,	0x82d8,	0x8250,	0x81c9,	0x8145,	0x80c2,	0x8040,	0xff02,	0xfd0e,
	0xfb25,	0xf947,	0xf773,	0xf5aa,	0xf3ea,	0xf234,	0xf087,	0xeee3,	0xed47,	0xebb3,	0xea27,
	0xe8a3,	0xe727,	0xe5b2,	0xe443,	0xe2dc,	0xe17a,	0xe020,	0xdecb,	0xdd7d,	0xdc34,	0xdaf1,
	0xd9b3,	0xd87b,	0xd748,	0xd61a,	0xd4f1,	0xd3cd,	0xd2ad,	0xd192,	0xd07b,	0xcf69,	0xce5b,
	0xcd51,	0xcc4a,	0xcb48,	0xca4a,	0xc94f,	0xc858,	0xc764,	0xc674,	0xc587,	0xc49d,	0xc3b7,
	0xc2d4,	0xc1f4,	0xc116,	0xc03c,	0xbf65,	0xbe90,	0xbdbe,	0xbcef,	0xbc23,	0xbb59,	0xba91,
	0xb9cc,	0xb90a,	0xb84a,	0xb78c,	0xb6d0,	0xb617,	0xb560,
};

static inline float eval_as_float(float x)
{
	float y = x;
	return y;
}

static const double one = 1.0, tiny = 1.0e-300;

#define __HI(x) *(1 + (int *)&x)
#define __LO(x) *(int *)&x
#define __HIp(x) *(1 + (int *)x)
#define __LOp(x) *(int *)x

double sun_ieee754_sqrt(double x)
{
	double z;
	int sign = (int)0x80000000;
	unsigned r, t1, s1, ix1, q1;
	int ix0, s0, q, m, t, i;

	ix0 = __HI(x); /* high word of x */
	ix1 = __LO(x); /* low word of x */

	/* take care of Inf and NaN */
	if ((ix0 & 0x7ff00000) == 0x7ff00000)
	{
		return x * x + x; /* sqrt(NaN)=NaN, sqrt(+inf)=+inf
					 sqrt(-inf)=sNaN */
	}
	/* take care of zero */
	if (ix0 <= 0)
	{
		if (((ix0 & (~sign)) | ix1) == 0)
			return x; /* sqrt(+-0) = +-0 */
		else if (ix0 < 0)
			return (x - x) / (x - x); /* sqrt(-ve) = sNaN */
	}
	/* normalize x */
	m = (ix0 >> 20);
	if (m == 0)
	{ /* subnormal x */
		while (ix0 == 0)
		{
			m -= 21;
			ix0 |= (ix1 >> 11);
			ix1 <<= 21;
		}
		for (i = 0; (ix0 & 0x00100000) == 0; i++)
			ix0 <<= 1;
		m -= i - 1;
		ix0 |= (ix1 >> (32 - i));
		ix1 <<= i;
	}
	m -= 1023; /* unbias exponent */
	ix0 = (ix0 & 0x000fffff) | 0x00100000;
	if (m & 1)
	{ /* odd m, double x to make it even */
		ix0 += ix0 + ((ix1 & sign) >> 31);
		ix1 += ix1;
	}
	m >>= 1; /* m = [m/2] */

	/* generate sqrt(x) bit by bit */
	ix0 += ix0 + ((ix1 & sign) >> 31);
	ix1 += ix1;
	q = q1 = s0 = s1 = 0; /* [q,q1] = sqrt(x) */
	r = 0x00200000;		  /* r = moving bit from right to left */

	while (r != 0)
	{
		t = s0 + r;
		if (t <= ix0)
		{
			s0 = t + r;
			ix0 -= t;
			q += r;
		}
		ix0 += ix0 + ((ix1 & sign) >> 31);
		ix1 += ix1;
		r >>= 1;
	}

	r = sign;
	while (r != 0)
	{
		t1 = s1 + r;
		t = s0;
		if ((t < ix0) || ((t == ix0) && (t1 <= ix1)))
		{
			s1 = t1 + r;
			if (((t1 & sign) == sign) && (s1 & sign) == 0)
				s0 += 1;
			ix0 -= t;
			if (ix1 < t1)
				ix0 -= 1;
			ix1 -= t1;
			q1 += r;
		}
		ix0 += ix0 + ((ix1 & sign) >> 31);
		ix1 += ix1;
		r >>= 1;
	}

	/* use floating add to find out rounding direction */
	if ((ix0 | ix1) != 0)
	{
		z = one - tiny; /* trigger inexact flag */
		if (z >= one)
		{
			z = one + tiny;
			if (q1 == (unsigned)0xffffffff)
			{
				q1 = 0;
				q += 1;
			}
			else if (z > one)
			{
				if (q1 == (unsigned)0xfffffffe)
					q += 1;
				q1 += 2;
			}
			else
				q1 += (q1 & 1);
		}
	}
	ix0 = (q >> 1) + 0x3fe00000;
	ix1 = q1 >> 1;
	if ((q & 1) == 1)
		ix1 |= sign;
	ix0 += (m << 20);
	__HI(z) = ix0;
	__LO(z) = ix1;
	return z;
}

inline float sqrtf_alt(float x)
{
	uint32_t ix, m, m1, m0, even, ey;

	ix = asuint(x);
	if (predict_false(ix - 0x00800000 >= 0x7f800000 - 0x00800000))
	{
		/* x < 0x1p-126 or inf or nan.  */
		if (ix * 2 == 0)
			return x;
		if (ix == 0x7f800000)
			return x;
		if (ix > 0x7f800000)
			return __math_invalidf(x);
		/* x is subnormal, normalize it.  */
		ix = asuint(x * 0x1p23f);
		ix -= 23 << 23;
	}

	/* x = 4^e m; with int e and m in [1, 4).  */
	even = ix & 0x00800000;
	m1 = (ix << 8) | 0x80000000;
	m0 = (ix << 7) & 0x7fffffff;
	m = even ? m0 : m1;

	/* 2^e is the exponent part of the return value.  */
	ey = ix >> 1;
	ey += 0x3f800000 >> 1;
	ey &= 0x7f800000;

	/* compute r ~ 1/sqrt(m), s ~ sqrt(m) with 2 goldschmidt iterations.  */
	static const uint32_t three = 0xc0000000;
	uint32_t r, s, d, u, i;
	i = (ix >> 17) % 128;
	r = (uint32_t)__rsqrt_tab[i] << 16;
	/* |r*sqrt(m) - 1| < 0x1p-8 */
	s = mul32(m, r);
	/* |s/sqrt(m) - 1| < 0x1p-8 */
	d = mul32(s, r);
	u = three - d;
	r = mul32(r, u) << 1;
	/* |r*sqrt(m) - 1| < 0x1.7bp-16 */
	s = mul32(s, u) << 1;
	/* |s/sqrt(m) - 1| < 0x1.7bp-16 */
	d = mul32(s, r);
	u = three - d;
	s = mul32(s, u);
	/* -0x1.03p-28 < s/sqrt(m) - 1 < 0x1.fp-31 */
	s = (s - 1) >> 6;
	/* s < sqrt(m) < s + 0x1.08p-23 */

	/* compute nearest rounded result.  */
	uint32_t d0, d1, d2;
	float y, t;
	d0 = (m << 16) - s * s;
	d1 = s - d0;
	d2 = d1 + s + 1;
	s += d1 >> 31;
	s &= 0x007fffff;
	s |= ey;
	y = asfloat(s);
	if (FENV_SUPPORT)
	{
		/* handle rounding and inexact exception. */
		uint32_t tiny = predict_false(d2 == 0) ? 0 : 0x01000000;
		tiny |= (d1 ^ d2) & 0x80000000;
		t = asfloat(tiny);
		y = eval_as_float(y + t);
	}
	return y;
}

inline double sqrt_alt(double x)
{
	uint64_t ix, top, m;

	/* special case handling.  */
	ix = asuint64(x);
	top = ix >> 52;
	if (predict_false(top - 0x001 >= 0x7ff - 0x001))
	{
		/* x < 0x1p-1022 or inf or nan.  */
		if (ix * 2 == 0)
			return x;
		if (ix == 0x7ff0000000000000)
			return x;
		if (ix > 0x7ff0000000000000)
			return __math_invalid(x);
		/* x is subnormal, normalize it.  */
		ix = asuint64(x * 0x1p52);
		top = ix >> 52;
		top -= 52;
	}

	/* argument reduction:
	   x = 4^e m; with integer e, and m in [1, 4)
	   m: fixed point representation [2.62]
	   2^e is the exponent part of the result.  */
	int even = top & 1;
	m = (ix << 11) | 0x8000000000000000;
	if (even)
		m >>= 1;
	top = (top + 0x3ff) >> 1;

	/* Approximate r ~ 1/sqrt(m) and s ~ sqrt(m) when m in [1,4)

	   initial estimate:
	   7bit table lookup (1bit exponent and 6bit significand).

	   iterative Approximation:
	   using 2 goldschmidt iterations with 32bit int arithmetics
	   and a final iteration with 64bit int arithmetics.

	   details:

	   the relative error (e = r0 sqrt(m)-1) of a linear estimate
	   (r0 = a m + b) is |e| < 0.085955 ~ 0x1.6p-4 at best,
	   a table lookup is faster and needs one less iteration
	   6 bit lookup table (128b) gives |e| < 0x1.f9p-8
	   7 bit lookup table (256b) gives |e| < 0x1.fdp-9
	   for single and double prec 6bit is enough but for quad
	   prec 7bit is needed (or modified iterations). to avoid
	   one more iteration >=13bit table would be needed (16k).

	   a newton-raphson iteration for r is
		 w = r*r
		 u = 3 - m*w
		 r = r*u/2
	   can use a goldschmidt iteration for s at the end or
		 s = m*r

	   first goldschmidt iteration is
		 s = m*r
		 u = 3 - s*r
		 r = r*u/2
		 s = s*u/2
	   next goldschmidt iteration is
		 u = 3 - s*r
		 r = r*u/2
		 s = s*u/2
	   and at the end r is not computed only s.

	   they use the same amount of operations and converge at the
	   same quadratic rate, i.e. if
		 r1 sqrt(m) - 1 = e, then
		 r2 sqrt(m) - 1 = -3/2 e^2 - 1/2 e^3
	   the advantage of goldschmidt is that the mul for s and r
	   are independent (computed in parallel), however it is not
	   "self synchronizing": it only uses the input m in the
	   first iteration so rounding errors accumulate. at the end
	   or when switching to larger precision arithmetics rounding
	   errors dominate so the first iteration should be used.

	   the fixed point representations are
		 m: 2.30 r: 0.32, s: 2.30, d: 2.30, u: 2.30, three: 2.30
	   and after switching to 64 bit
		 m: 2.62 r: 0.64, s: 2.62, d: 2.62, u: 2.62, three: 2.62  */

	static const uint64_t three = 0xc0000000;
	uint64_t r, s, d, u, i;

	i = (ix >> 46) % 128;
	r = (uint32_t)__rsqrt_tab[i] << 16;
	/* |r sqrt(m) - 1| < 0x1.fdp-9 */
	s = mul32(m >> 32, r);
	/* |s/sqrt(m) - 1| < 0x1.fdp-9 */
	d = mul32(s, r);
	u = three - d;
	r = mul32(r, u) << 1;
	/* |r sqrt(m) - 1| < 0x1.7bp-16 */
	s = mul32(s, u) << 1;
	/* |s/sqrt(m) - 1| < 0x1.7bp-16 */
	d = mul32(s, r);
	u = three - d;
	r = mul32(r, u) << 1;
	/* |r sqrt(m) - 1| < 0x1.3704p-29 (measured worst-case) */
	r = r << 32;
	s = mul64(m, r);
	d = mul64(s, r);
	u = (three << 32) - d;
	s = mul64(s, u); /* repr: 3.61 */
	/* -0x1p-57 < s - sqrt(m) < 0x1.8001p-61 */
	s = (s - 2) >> 9; /* repr: 12.52 */
	/* -0x1.09p-52 < s - sqrt(m) < -0x1.fffcp-63 */

	/* s < sqrt(m) < s + 0x1.09p-52,
	   compute nearest rounded result:
	   the nearest result to 52 bits is either s or s+0x1p-52,
	   we can decide by comparing (2^52 s + 0.5)^2 to 2^104 m.  */
	uint64_t d0, d1, d2;
	double y, t;
	d0 = (m << 42) - s * s;
	d1 = s - d0;
	d2 = d1 + s + 1;
	s += d1 >> 63;
	s &= 0x000fffffffffffff;
	s |= top << 52;
	y = asdouble(s);
	if (FENV_SUPPORT)
	{
		/* handle rounding modes and inexact exception:
		   only (s+1)^2 == 2^42 m case is exact otherwise
		   add a tiny value to cause the fenv effects.  */
		uint64_t tiny = predict_false(d2 == 0) ? 0 : 0x0010000000000000;
		tiny |= (d1 ^ d2) & 0x8000000000000000;
		t = asdouble(tiny);
		y = eval_as_double(y + t);
	}
	return y;
}

float SQRT_Blinn(float x)
{
	union
	{
		float x;
		unsigned i;
	} u;
	u.x = x;
	u.i = (u.i >> 1) + 0x1fc00000;
	return u.x;
}

float SQRT_Heron_Muller(float x)
{
	float y;
	int i = *(int *)&x;
	i = 0x1fbb4ecc + (i >> 1);
	y = *(float *)&i;
	y = 0.5f * (y + x / y);
	y = 0.5f * (y + x / y);
	return y;
}

float SQRT_Blinn_Modified(float x)
{
	union
	{
		float x;
		unsigned i;
	} u;
	u.x = x;
	u.i = (u.i >> 1) + 0x1fbb4f2e;
	return u.x;
}

float SQRT_Modified_Heron_1(float x)
{
	float y;
	int i = *(int *)&x;
	i = 0x1fbb67af + (i >> 1);
	y = *(float *)&i;
	y = 0.5f * (y + x / y);
	y = 0.5f * (y + x / y);
	return y;
}

float SQRT_Modified_Heron_2(float x)
{
	float y;
	int i = *(int *)&x;
	i = 0x1fbb67af + (i >> 1);
	y = *(float *)&i;
	y = 0.499849794299670f * (y + x / y);
	y = 0.5f * (y + x / y);
	return y;
}

float SQRT_2segments(float x)
{
	int i = *(int *)&x;
	int k = i & 0x00800000;
	float y;
	if (k == 0)
	{
		i = 0x1f9a827a + (i >> 1);
		y = *(float *)&i;
		y = 1.18035706419541798f * y;
	}
	else
	{
		i = 0x1f5a827a + (i >> 1);
		y = *(float *)&i;
		y = 1.6692769686280501095f * y;
	}
	return y;
}

float SQRT_Heron_2segments(float x)
{
	int i = *(int *)&x;
	int k = i & 0x00800000;
	float y;
	if (k == 0)
	{
		i = 0x1f9a827a + (i >> 1);
		y = *(float *)&i;
		y = 1.18035706419541798f * y;
	}
	else
	{
		i = 0x1f5a827a + (i >> 1);
		y = *(float *)&i;
		y = 1.6692769686280501095f * y;
	}
	y = 0.4999930253152879213f * (y + x / y);
	return y;
}

const float kk0[16] = {1.3728804844963743741743109895869174, 1.2984464325688431991846789745811575, 1.2349522866656504095676954218143650, 1.1799541552589359812272435026388901, 1.1317105556304312508949849916223526, 1.0889423218359534849831706863530610,
					   1.0506858108072537800493465016626868, 1.0161993590210952468964805394085166, 1.9415462006921182911486340105462846, 1.8362805549538204860640915291539554, 1.7464862726862291524227673452809011, 1.6687071693456759394814332790086739, 1.6004804164533469399066344222701610, 1.5399970001824531463719726207375215, 1.4858941234365901375799250869156190, 1.4371229156024788917009615207303487};

const int RR[16] = {0x1F83E1DC, 0x1F8BE509, 0x1F93E79B, 0x1F9BE9BB, 0x1FA3EB84, 0x1FABED08, 0x1FB3EE57, 0x1FBBEF7B, 0x1F43E1DC, 0x1F4BE509, 0x1F53E79B, 0x1F5BE9BB, 0x1F63EB84, 0x1F6BED08, 0x1F73EE57, 0x1F7BEF7B};

float SQRT_16segments(float x)
{
	float y;
	u_int32_t i, j, i_mx;
	i = *(int *)&x;
	i_mx = i & 0x00ffffff;
	j = i_mx >> 20;
	i = RR[j] + (i >> 1);
	y = *(float *)&i;
	y = kk0[j] * y;
	return y;
}
float SQRT_Heron_16segments(float x)
{
	float y;
	u_int32_t i, j, i_mx;
	i = *(int *)&x;
	i_mx = i & 0x00ffffff;
	j = i_mx >> 20;
	i = RR[j] + (i >> 1);
	y = *(float *)&i;
	y = kk0[j] * y;
	y = 0.5f * (y + x / y);

	return y;
}

float SQRT_10bits(float x)
{
	int i = *(int *)&x;
	i = 0x5f0b3892 - (i >> 1);
	float y = *(float *)&i;
	float c = x * y;
	y = c * (1.89099014875f - c * y);
	return y;
}

const float k0[2] = {0.88601269f, 1.25302145f};
const float k1[2] = {0.103027083f, 0.291411832f};
const int R[2] = {0x5f99e8b6, 0x5f59e8b6};
float SQRT_13bits(float x)
{
	float y, c;
	int i = *(int *)&x;
	int j = (i & 0x00800000) >> 23;
	i = R[j] - (i >> 1);
	y = *(float *)&i;
	c = x * y;
	y = c * (k0[j] - k1[j] * c * y);
	return y;
}

float SQRT_15bits(float x)
{
	int i = *(int *)&x;
	i = 0x5f1110a0 - (i >> 1);
	float y = *(float *)&i;
	float c = x * y;
	float d = c * y;
	y = c * (2.2825186f - d * (2.2533049f - d));
	return y;
}

float SQRT_23bits(float x)
{
	int i = *(int *)&x;
	i = 0x5f1110a0 - (i >> 1);
	float y = *(float *)&i;
	float c = x * y * y;
	y = y * (2.2825186f - c * (2.2533049f - c));
	c = x * y;
	y = c * (1.5f - 0.5f * c * y);
	return y;
}

template <class T, class F>
void profileExp(const std::string &desc, long int iterations, T &testVal, F func)
{
	auto iter = iterations;
	while (iter--)
		func(testVal);
	iter = iterations;
	auto start = high_resolution_clock::now();
	while (iter--)
		func(testVal);
	auto stop = high_resolution_clock::now();
	auto time_eval = duration_cast<nanoseconds>(stop - start);
	std::cout << std::left << std::setw(35) << desc
			  << time_eval.count() / iterations << " ns" << std::endl;
}

template <class T, class F>
void profileExpCycles(const std::string &desc, long int iterations, T &testVal, F func)
{
	auto iter = iterations;
	while (iter--)
		func(testVal);
	iter = iterations;
	unsigned long long t = __builtin_readcyclecounter();
	while (iter--)
		func(testVal);
	t = __builtin_readcyclecounter() - t;
	std::cout << std::left << std::setw(35) << desc << t / (double)iterations
			  << " cycles" << std::endl;
}

template <class T, class F>
void calculateExpRMSD(const std::string &desc, F func)
{
	T currentValue = T(1.0f);
	T maxValue = T(4.f);
	int count = 0;
	double RMSD = 0;

	double maxPoh = 0.0, maxValx = 0.0, maxValy = 0.0;
	double minPoh = 0.0, minValx = 0.0, minValy = 0.0;

	while (currentValue < maxValue)
	{
		currentValue = nextafterf(currentValue, maxValue);
		count++;

		auto ref = sqrtf(currentValue);
		auto cal = func(currentValue);
		double vidn = (double)cal / double(sqrtf(currentValue)) - 1;
		maxPoh = std::max(maxPoh, vidn);
		minPoh = std::min(minPoh, vidn);
		RMSD += std::pow(ref - cal, 2);
		// std::cout <<  std::setprecision(20) << currentValue <<std::endl;
	}
	std::streamsize base = std::cout.precision();
	std::cout << std::left
			  << std::setw(35) << desc
			  << std::setw(17) << std::setprecision(base) << std::scientific << sqrtf(RMSD / count)
			  << std::setw(16) << std::setprecision(4) << std::fixed << -log2(maxPoh)
			  << std::setw(17) << std::setprecision(base) << std::scientific << maxPoh
			  << std::setw(17) << std::setprecision(base) << std::scientific << minPoh << std::endl;
}

template <class T, class F>
void calculateExpRMSD_half(const std::string &desc, F func)
{
	T currentValue = T(1.f);
	T maxValue = T(4.f);
	int count = 0;
	double RMSD = 0;

	double maxPoh = 0.0, maxValx = 0.0, maxValy = 0.0;
	double minPoh = 0.0, minValx = 0.0, minValy = 0.0;

	while (currentValue < maxValue)
	{
		currentValue = half_float::nextafter(currentValue, maxValue);
		count++;

		auto ref = sqrtf(currentValue);
		auto cal = func(currentValue);
		double vidn = (double)(double(cal) / double(ref)) - 1;
		maxPoh = std::max(maxPoh, vidn);
		minPoh = std::min(minPoh, vidn);
		RMSD += std::pow(ref - cal, 2);
		// std::cout <<  std::setprecision(20) << currentValue <<std::endl;
	}
	std::streamsize base = std::cout.precision();
	std::cout << std::left
			  << std::setw(35) << desc
			  << std::setw(17) << std::setprecision(base) << std::scientific << sqrtf(RMSD / count)
			  << std::setw(16) << std::setprecision(4) << std::fixed << -log2(maxPoh)
			  << std::setw(17) << std::setprecision(base) << std::scientific << maxPoh
			  << std::setw(17) << std::setprecision(base) << std::scientific << minPoh << std::endl;
}

int main()
{
	float step = nextafterf(1.0f, 4.f) - 1.0f;
	half steph = half(step);

	std::cout << std::endl
			  << "Step: " << step << " " << std::endl;

	std::cout << "Execution time:" << std::endl;

	profileExp("SQRT_Blinn", iterationsCount, step, SQRT_Blinn);
	profileExp("SQRT_Blinn_Modified", iterationsCount, step, SQRT_Blinn_Modified);
	profileExp("SQRT_Heron_Muller", iterationsCount, step, SQRT_Heron_Muller);
	profileExp("SQRT_Modified_Heron_1", iterationsCount, step, SQRT_Modified_Heron_1);
	profileExp("SQRT_Modified_Heron_2", iterationsCount, step, SQRT_Modified_Heron_2);
	profileExp("SQRT_2segments ", iterationsCount, step, SQRT_2segments);
	profileExp("SQRT_Heron_2segments ", iterationsCount, step, SQRT_Heron_2segments);
	profileExp("SQRT_16segments", iterationsCount, step, SQRT_16segments);
	profileExp("SQRT_Heron_16segments", iterationsCount, step, SQRT_Heron_16segments);
	profileExp("SQRT_10bits", iterationsCount, step, SQRT_10bits);
	profileExp("SQRT_13bits", iterationsCount, step, SQRT_13bits);
	profileExp("SQRT_15bits", iterationsCount, step, SQRT_15bits);
	profileExp("SQRT_23bits", iterationsCount, step, SQRT_23bits);
	profileExp("sqrt_alt", iterationsCount, step, sqrt_alt);
	profileExp("sqrtf_alt", iterationsCount, step, sqrtf_alt);
	profileExp("sun_ieee754_sqrt", iterationsCount, step, sun_ieee754_sqrt);
	profileExp("std::sqrtf", iterationsCount, step, sqrtf);
	profileExp<float, float(float)>("std::sqrt", iterationsCount, step, std::sqrt);

	std::cout << std::endl
			  << "Number of cycles:" << std::endl;

	profileExpCycles("SQRT_Blinn", iterationsCount, step, SQRT_Blinn);
	profileExpCycles("SQRT_Blinn_Modified", iterationsCount, step, SQRT_Blinn_Modified);
	profileExpCycles("SQRT_Heron_Muller", iterationsCount, step, SQRT_Heron_Muller);
	profileExpCycles("SQRT_Modified_Heron_1", iterationsCount, step, SQRT_Modified_Heron_1);
	profileExpCycles("SQRT_Modified_Heron_2", iterationsCount, step, SQRT_Modified_Heron_2);
	profileExpCycles("SQRT_2segments ", iterationsCount, step, SQRT_2segments);
	profileExpCycles("SQRT_Heron_2segments ", iterationsCount, step, SQRT_Heron_2segments);
	profileExpCycles("SQRT_16segments", iterationsCount, step, SQRT_16segments);
	profileExpCycles("SQRT_Heron_16segments", iterationsCount, step, SQRT_Heron_16segments);
	profileExpCycles("SQRT_10bits", iterationsCount, step, SQRT_10bits);
	profileExpCycles("SQRT_13bits", iterationsCount, step, SQRT_13bits);
	profileExpCycles("SQRT_15bits", iterationsCount, step, SQRT_15bits);
	profileExpCycles("SQRT_23bits", iterationsCount, step, SQRT_23bits);
	profileExpCycles("sqrt_alt", iterationsCount, step, sqrt_alt);
	profileExpCycles("sqrtf_alt", iterationsCount, step, sqrtf_alt);
	profileExpCycles("sun_ieee754_sqrt", iterationsCount, step, sun_ieee754_sqrt);
	profileExpCycles("std::sqrtf", iterationsCount, step, sqrtf);
	profileExpCycles<float, float(float)>("std::sqrt", iterationsCount, step, std::sqrt);

	std::cout << std::endl
			  << std::left
			  << std::setw(35) << "NAME"
			  << std::setw(17) << "RMSD"
			  << std::setw(17) << "LSB"
			  << std::setw(17) << "MAX REL ERROR"
			  << std::setw(17) << "MIN REL ERROR" << std::endl;

	calculateExpRMSD<float>("SQRT_Blinn", SQRT_Blinn);
	calculateExpRMSD<float>("SQRT_Blinn_Modified", SQRT_Blinn_Modified);
	calculateExpRMSD<float>("SQRT_Heron_Muller", SQRT_Heron_Muller);
	calculateExpRMSD<float>("SQRT_Modified_Heron_1", SQRT_Modified_Heron_1);
	calculateExpRMSD<float>("SQRT_Modified_Heron_2", SQRT_Modified_Heron_2);
	calculateExpRMSD<float>("SQRT_2segments ", SQRT_2segments);
	calculateExpRMSD<float>("SQRT_Heron_2segments ", SQRT_Heron_2segments);
	calculateExpRMSD<float>("SQRT_16segments", SQRT_16segments);
	calculateExpRMSD<float>("SQRT_Heron_16segments", SQRT_Heron_16segments);
	calculateExpRMSD<float>("SQRT_10bits", SQRT_10bits);
	calculateExpRMSD<float>("SQRT_13bits", SQRT_13bits);
	calculateExpRMSD<float>("SQRT_15bits", SQRT_15bits);
	calculateExpRMSD<float>("SQRT_23bits", SQRT_23bits);
	calculateExpRMSD<float>("sqrt_alt", sqrt_alt);
	calculateExpRMSD<float>("sqrtf_alt", sqrtf_alt);
	calculateExpRMSD<double>("sun_ieee754_sqrt", sun_ieee754_sqrt);
	calculateExpRMSD<float>("std::sqrtf", sqrtf);
	calculateExpRMSD<float, float(float)>("std::sqrt", std::sqrt);

	return 0;
}