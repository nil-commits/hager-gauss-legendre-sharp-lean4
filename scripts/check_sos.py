import numpy as np

# 1. Verify exact algebraic identity for 144 * L3(x, u) >= 9 on x in [0, 1/12], u in [0, 3]
us = np.linspace(0.0, 3.0, 500)
xs = np.linspace(0.0, 1.0/12.0, 200)
U, X = np.meshgrid(us, xs)
t = 12.0 * X
c1, c2, c3 = 1 - 2*X, 1 - 6*X, 1 - 12*X
L3_lhs = 144.0 * (1 - c1*U/2 + c1*c2*U**2/12 - c1*c2*c3*U**3/144)
L3_rhs = 9.0 + (3 - U)*((U - 4.5)**2 + 99.0/4.0) + X*U*(12*t*(3 - U)*(4 - U) + (1 - t)*((4*U - 12)**2 + (4 - t)*U**2))
print(f"L3 identity max error: {np.max(np.abs(L3_lhs - L3_rhs)):.3e}")

# 2. Find an equally clean algebraic identity for -576 * U4(x, u) > 0 on x in [0, 1/12], u in [1.6, 4.8] (or [1.6, 5.0])!
# U4(x, u) = 1 - u + c1*u^2/4 - c1*c2*u^3/36 + c1*c2*c3*u^4/576
# 576 * U4(x, u) = (576 - 576u + 144u^2 - 16u^3 + u^4)
#   + x * (-288 u^2 + 128 u^3 - 20 u^4)
#   + x^2 * (-192 u^3 + 108 u^4)
#   + x^3 * (-144 u^4)
# Wait: substitute t = 12 x in [0, 1] into the x, x^2, x^3 terms!
# Let D(x, u) = 576 * (U4(x, u) - U4(0, u))
# = x * u^2 * [ (-288 + 128 u - 20 u^2) + t * (-16 u + 9 u^2) - t^2 * u^2 ]
# WHOA!! CHECK THE SIGN OF THAT BRACKET FOR t in [0, 1], u in [1.6, 5.0]!!
us2 = np.linspace(1.6, 5.0, 500)
U2, X2 = np.meshgrid(us2, xs)
t2 = 12.0 * X2
c1_2, c2_2, c3_2 = 1 - 2*X2, 1 - 6*X2, 1 - 12*X2
U4_lhs = 576.0 * (1 - U2 + c1_2*U2**2/4 - c1_2*c2_2*U2**3/36 + c1_2*c2_2*c3_2*U2**4/576)
U4_0 = 576 - 576*U2 + 144*U2**2 - 16*U2**3 + U2**4
bracket = (-288 + 128*U2 - 20*U2**2) + t2*(-16*U2 + 9*U2**2) - (t2**2)*(U2**2)
U4_rhs = U4_0 + X2 * (U2**2) * bracket
print(f"U4 identity max error: {np.max(np.abs(U4_lhs - U4_rhs)):.3e}")
print(f"max bracket on [0, 1/12] x [1.6, 5.0]: {np.max(bracket):.6f}")
print(f"max bracket at t=0: {np.max(-288 + 128*us2 - 20*us2**2):.6f}")
print(f"max bracket at t=1: {np.max(-288 + 112*us2 - 12*us2**2):.6f}")
# WAIT A SECOND!! CHECK BOTH ENDPOINTS t=0 AND t=1!!
# At t=0: -288 + 128u - 20u^2 = -4*(5u^2 - 32u + 72) = -4*(5*(u - 3.2)^2 + 20.8) < 0 FOR ALL u!!
# At t=1: -288 + 112u - 12u^2 = -4*(3u^2 - 28u + 72) = -4*(3*(u - 14/3)^2 + 20/3) < 0 FOR ALL u!!
# AND THE QUADRATIC TERM IN t IS -t^2 u^2!
# Wait: rewrite bracket as convex combination of t=0 and t=1:
# bracket = (1 - t)*(-288 + 128u - 20u^2) + t*(-288 + 112u - 12u^2) + t*(1 - t)*u^2!!
# CHECK THAT!!
# (1-t)*(-20u^2) + t*(-12u^2) + t*(1-t)*u^2 = (-20 + 8t + t - t^2)u^2 = (-20 + 9t - t^2)u^2! EXACT!!
# Now absorb t*(1-t)*u^2 into (1-t)*(-288 + 128u - 20u^2):
# (1-t)*(-288 + 128u - (20 - t)*u^2) <= (1-t)*(-288 + 128u - 19*u^2)!
# Check discriminant of 19u^2 - 128u + 288: 128^2 - 4*19*288 = 16384 - 21888 = -5504 < 0!!
# SO bracket < 0 FOR ALL t in [0, 1] AND ALL u in R!!
br_check = (1 - t2)*(-288 + 128*U2 - (20 - t2)*U2**2) + t2*(-288 + 112*U2 - 12*U2**2)
print(f"bracket identity max error: {np.max(np.abs(bracket - br_check)):.3e}")

# AND CHECK U4_0 = 576 - 576u + 144u^2 - 16u^3 + u^4 on u in [1.6, 5.0]!!
# Factor or bound U4_0!
# What are the real roots of U4_0(u)?
roots = np.roots([1, -16, 144, -576, 576])
print("Roots of U4_0(u):", roots)
print(f"max U4_0 on [1.6, 5.0]: {np.max(U4_0):.6f} (at u=1.6: {576 - 576*1.6 + 144*1.6**2 - 16*1.6**3 + 1.6**4:.6f}, at u=5.0: {576 - 576*5 + 144*25 - 16*125 + 625:.6f})")
# Check U4_0 at u = 1.6 and u = 5.0:
# Wait: U4_0(u) = (u - 1.6)*(u - 5.0) * Q(u) + R(u)?
# Even simpler: check U4_0(u) = (u - 1.5)*(u - 5.2)*... or divide by (u - 1.5)*(u - 5.2)!
# Let's check U4_0(u) for u in [8/5, 5]:
# Divide u^4 - 16u^3 + 144u^2 - 576u + 576 by (u - 1.5)*(u - 5.2)? No, use nice rationals!
# Check U4_0(u) at u = 3/2 (1.5) and u = 5:
# At u=3/2: 576 - 864 + 324 - 54 + 81/16 = -18 + 5.0625 = -12.9375 < 0!
# At u=5: 576 - 2880 + 3600 - 2000 + 625 = -79 < 0!
# Wait: divide U4_0(u) by (u - 3/2)(u - 5) = u^2 - 13/2 u + 15/2!
# Let's compute polynomial division!
q, r = np.polydiv([1, -16, 144, -576, 576], [1, -6.5, 7.5])
print("Dividing U4_0 by (u - 3/2)(u - 5): quotient =", q, "remainder =", r)
# Check quotient q(u) = u^2 - 9.5u + 74.75: discriminant = 9.5^2 - 4*74.75 = 90.25 - 299 < 0! ALWAYS > 0!
# Check remainder r(u) on [1.5, 5.0]:
print(f"remainder at u=1.5: {np.polyval(r, 1.5):.6f}, at u=5.0: {np.polyval(r, 5.0):.6f}")
# BOTH ARE NEGATIVE!! Wait: r is LINEAR, negative at BOTH endpoints 1.5 and 5.0, so r(u) < 0 on ALL of [1.5, 5.0]!!
# OMG!! THAT MEANS U4_0(u) < 0 ON ALL OF [3/2, 5] IN ONE LINE!!
