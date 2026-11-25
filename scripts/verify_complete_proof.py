import numpy as np
from numpy.polynomial.legendre import leggauss

def verify_symbolic_certificates():
    print("=== ALGEBRAIC CERTIFICATES FOR LEMMA 2.1 AND LEMMA 2.2 ===")
    # x = 1/N in [0, 1/12] (for n >= 3, N = n(n+1) >= 12)
    # c1 = 1 - 2x, c2 = 1 - 6x, c3 = 1 - 12x
    us = np.linspace(0.0, 3.0, 1000)
    xs = np.linspace(0.0, 1.0/12.0, 400)
    U, X = np.meshgrid(us, xs)
    c1 = 1.0 - 2.0*X
    c2 = 1.0 - 6.0*X
    c3 = 1.0 - 12.0*X

    # Lemma 2.1: L3 = 1 - c1*u/2 + c1*c2*u^2/12 - c1*c2*c3*u^3/144
    # Drop c3 <= 1: L3 >= L3_simp = 1 - c1*u/2 + c1*c2*u^2/12 * (1 - u/12)
    L3 = 1.0 - c1*U/2.0 + c1*c2*(U**2)/12.0 - c1*c2*c3*(U**3)/144.0
    L3_simp = 1.0 - c1*U/2.0 + c1*c2*(U**2)/12.0 * (1.0 - U/12.0)
    L3_at_0 = 1.0 - U/2.0 + (U**2)/12.0 - (U**3)/144.0
    diff_L3 = L3_simp - L3_at_0
    # Compute exact formula for diff_L3 = L3_simp - L3_at_0:
    # -c1*u/2 - (-u/2) = +x*u
    # (c1*c2 - 1) = (1 - 8x + 12x^2) - 1 = -x(8 - 12x)
    # So diff_L3 = x * u * [ 1 - (8 - 12x) * u * (1 - u/12) / 12 ]
    # WAIT A SECOND! Check [ 1 - (8 - 12x) * u * (1 - u/12) / 12 ] on u in [0, 3], x in [0, 1/12]!
    # Since 8 - 12x <= 8 and u(1 - u/12) <= 3*(1 - 3/12) = 9/4 = 2.25:
    # (8 - 12x) * u * (1 - u/12) / 12 <= 8 * (9/4) / 12 = 18/12 = 1.5 > 1! Oh, check min of diff_L3!
    print(f"min L3 on [0,1/12]x[0,3]: {np.min(L3):.6f}")
    print(f"min L3_simp on [0,1/12]x[0,3]: {np.min(L3_simp):.6f}")
    print(f"min (L3_simp - L3_at_0) on [0,1/12]x[0,3]: {np.min(diff_L3):.6f}")
    # Check where min of L3_simp is achieved!
    idx = np.unravel_index(np.argmin(L3_simp), L3_simp.shape)
    print(f"argmin L3_simp: x={xs[idx[0]]:.6f}, u={us[idx[1]]:.6f}, val={L3_simp[idx]:.6f}")
    # Check min of L3_simp at u = 3 as function of x:
    # At u = 3: 1 - 1.5(1-2x) + (9/12)(3/4)(1-2x)(1-6x) = -0.5 + 3x + (9/16)(1 - 8x + 12x^2)
    # = (1/16) - (3/2)x + (27/4)x^2 = 1/16 - 1.5x + 6.75x^2!
    # Wait: at x = 1/12: 1/16 - 1/8 + 27/576 = 36/576 - 72/576 + 27/576 = -9/576 < 0!
    # AHA!! Catch that!! Dropping c3 to 1 made L3_simp slightly negative at x = 1/12 (n=3),
    # whereas EXACT L3 (with c3 = 1 - 12x = 0 at n=3!) had min = +0.0625!!
    idx_e = np.unravel_index(np.argmin(L3), L3.shape)
    print(f"argmin EXACT L3: x={xs[idx_e[0]]:.6f}, u={us[idx_e[1]]:.6f}, val={L3[idx_e]:.6f}")
    # Check L3 - L3_at_0 for EXACT L3!
    diff_L3_exact = L3 - L3_at_0
    print(f"min (EXACT L3 - L3_at_0) on [0,1/12]x[0,3]: {np.min(diff_L3_exact):.6f}")

    # --- Lemma 2.2: U4(x, u) < 0 on u in [1.6, 4.8] ---
    print("\n--- Lemma 2.2: U4(x, u) < 0 ---")
    for u_hi in [4.5, 4.8, 5.0]:
        us2 = np.linspace(1.6, u_hi, 1000)
        U2, X2 = np.meshgrid(us2, xs)
        c1_2 = 1.0 - 2.0*X2
        c2_2 = 1.0 - 6.0*X2
        c3_2 = 1.0 - 12.0*X2
        U4 = 1.0 - U2 + c1_2*(U2**2)/4.0 - c1_2*c2_2*(U2**3)/36.0 + c1_2*c2_2*c3_2*(U2**4)/576.0
        U4_0 = 1.0 - U2 + (U2**2)/4.0 - (U2**3)/36.0 + (U2**4)/576.0
        print(f"u in [1.6, {u_hi}]: max U4={np.max(U4):.6f}, max U4(0,u)={np.max(U4_0):.6f}, max(U4 - U4(0,u))={np.max(U4 - U4_0):.6f}")


def verify_full_n500():
    print("\n=== FULL NUMERICAL VERIFICATION FOR n = 1..500 ===")
    min_ratio_p2 = float('inf')
    max_R_p3 = 0.0
    max_E_ratio = 0.0
    max_gauss_l1_excess = -float('inf')
    max_radau_l1_excess = -float('inf')
    max_diag_err = 0.0

    for n in range(1, 501):
        N = n * (n + 1)
        tau, w = leggauss(n)
        # Compute P_n'(tau_j) via recurrence (stable for high n!)
        # P_{k+1}(t) = ((2k+1)t P_k(t) - k P_{k-1}(t)) / (k+1)
        # (1 - t^2) P_n'(t) = n (P_{n-1}(t) - t P_n(t)) = n P_{n-1}(t) at t = tau_j!
        P_prev = np.ones_like(tau)
        P_curr = tau.copy()
        for k in range(1, n):
            P_next = ((2*k + 1) * tau * P_curr - k * P_prev) / (k + 1)
            P_prev, P_curr = P_curr, P_next
        # Now P_prev = P_{n-1}(tau), P_curr = P_n(tau) ~ 0
        # For n = 1, P_prev = P_0 = 1, P_curr = P_1 = tau = 0
        if n == 1:
            P_nm1 = np.ones_like(tau)
        else:
            P_nm1 = P_prev
        one_minus_t2_dp = n * P_nm1  # (1 - tau_j^2) P_n'(tau_j)
        dp = one_minus_t2_dp / (1.0 - tau**2)

        # Check energy bound E(tau_j) = (1 - tau_j^2) P_n'(tau_j)^2 <= N
        E_vals = (1.0 - tau**2) * dp**2
        max_E_ratio = max(max_E_ratio, np.max(E_vals / N))

        if n >= 2:
            ratio_p2 = (1.0 - tau[-2]) / (1.0 - tau[-1])
            min_ratio_p2 = min(min_ratio_p2, ratio_p2)

        if n >= 3:
            # Check Part 3 bound for all j <= n-2 with n-j even (0-indexed: j <= n-3, (n-1-j) even)
            s_n = 1.0 - tau[-1]
            for j in range(n - 2):
                if (n - 1 - j) % 2 == 0:
                    s_j = 1.0 - tau[j]
                    # R_exact = (1-tau_j^2)*dp_j * (1-tau_n^2)*dp_n / (2*N*(tau_n - tau_j))
                    R_ex = one_minus_t2_dp[j] * one_minus_t2_dp[-1] / (2.0 * N * (tau[-1] - tau[j]))
                    R_energy = np.sqrt((1.0 - tau[j]**2) * (1.0 - tau[-1]**2)) / (2.0 * (tau[-1] - tau[j]))
                    R_simple = np.sqrt(s_j * s_n) / (s_j - s_n)
                    assert R_ex <= R_energy + 1e-12
                    assert R_energy <= R_simple + 1e-12
                    assert R_simple < 1.0
                    max_R_p3 = max(max_R_p3, R_simple)

        # For n <= 120, also verify full matrix A (Gauss and Radau) directly!
        if n <= 120:
            # Gauss matrix A via Legendre expansion
            P = np.zeros((n + 1, n))
            P[0, :] = 1.0
            P[1, :] = tau
            for k in range(1, n):
                P[k + 1, :] = ((2*k + 1) * tau * P[k, :] - k * P[k - 1, :]) / (k + 1)
            # K[i, j] = 0.5*(1+tau_i) + 0.5 * sum_{k=1}^{n-1} P_k(tau_j)*(P_{k+1}(tau_i) - P_{k-1}(tau_i))
            diffP = P[2:n+1, :] - P[0:n-1, :]  # shape (n-1, n), row k-1 is P_{k+1} - P_{k-1}
            K = 0.5 * (1.0 + tau[:, None]) + 0.5 * (diffP.T @ P[1:n, :])
            A = K * w[None, :]
            diag_err = np.max(np.abs(np.diag(A) - 0.5 * w))
            max_diag_err = max(max_diag_err, diag_err)
            # Check last row A[-1, :] >= 0
            assert np.min(A[-1, :]) > -1e-14, f"Negative entry in last row at n={n}: {np.min(A[-1,:])}"
            row_l1 = np.sum(np.abs(A), axis=1)
            # Check Part 1 bound: row_l1 <= (3 + tau)/2
            assert np.all(row_l1 <= (3.0 + tau) / 2.0 + 1e-12)
            # Check target bound: row_l1 <= 1 + tau_n
            max_gauss_l1_excess = max(max_gauss_l1_excess, np.max(row_l1 - (1.0 + tau[-1])))

            # Radau nodes: roots of P_n(t) - P_{n-1}(t) = 0 (includes tau_n = 1)
            if n == 1:
                tau_r = np.array([1.0])
                w_r = np.array([2.0])
            else:
                # Roots of P_n - P_{n-1} via Golub-Welsch for Jacobi(1, 0) on n-1 points + {1}
                # Tridiagonal Jacobi matrix for P_k^{(1, 0)} (alpha=1, beta=0):
                m = n - 1
                k_arr = np.arange(m, dtype=float)
                # alpha_k = (beta^2 - alpha^2) / ((2k+a+b)(2k+a+b+2)) = -1 / ((2k+1)(2k+3))
                diag_j = -1.0 / ((2*k_arr + 1.0) * (2*k_arr + 3.0))
                k_sub = np.arange(1, m, dtype=float)
                # b_k^2 = 4 k (k+a)(k+b)(k+a+b) / ((2k+a+b)^2 (2k+a+b+1)(2k+a+b-1))
                # with a=1, b=0: 4 k^2 (k+1)^2 / ((2k+1)^2 (2k+2)(2k)) = k(k+1) / (2k+1)^2
                off_j = np.sqrt(k_sub * (k_sub + 1.0)) / (2*k_sub + 1.0)
                J = np.diag(diag_j) + np.diag(off_j, 1) + np.diag(off_j, -1)
                eigvals, eigvecs = np.linalg.eigh(J)
                # mu_0 = int_{-1}^1 (1-t) dt = 2
                w_jac = 2.0 * (eigvecs[0, :] ** 2)
                w_int = w_jac / (1.0 - eigvals)
                tau_r = np.append(eigvals, 1.0)
                w_r = np.append(w_int, 2.0 / (n * n))
            # Radau integration matrix via exact Legendre expansion!
            Pr = np.zeros((n + 1, n))
            Pr[0, :] = 1.0
            Pr[1, :] = tau_r
            for k in range(1, n):
                Pr[k + 1, :] = ((2*k + 1) * tau_r * Pr[k, :] - k * Pr[k - 1, :]) / (k + 1)
            diffPr = Pr[2:n+1, :] - Pr[0:n-1, :]
            Kr = 0.5 * (1.0 + tau_r[:, None]) + 0.5 * (diffPr.T @ Pr[1:n, :])
            Ar = Kr * w_r[None, :]
            row_l1_r = np.sum(np.abs(Ar), axis=1)
            assert np.all(row_l1_r <= (3.0 + tau_r) / 2.0 + 1e-11)
            max_radau_l1_excess = max(max_radau_l1_excess, np.max(row_l1_r - 2.0))

    print(f"n=1..500: max E(tau_j)/N = {max_E_ratio:.8f} (bound <= 1.0)")
    print(f"n=2..500: min (1-tau_{{n-1}})/(1-tau_n) = {min_ratio_p2:.8f} (bound >= 3.0 > 2.0)")
    print(f"n=3..500: max sqrt(s_j*s_n)/(s_j - s_n) (j<=n-2, n-j even) = {max_R_p3:.8f} (bound < 1.0)")
    print(f"n=1..120: max |A_ii - w_i/2| = {max_diag_err:.3e}")
    print(f"n=1..120: max Gauss (||A||_inf - (1+tau_n)) = {max_gauss_l1_excess:.3e}")
    print(f"n=1..120: max Radau (||A||_inf - 2) = {max_radau_l1_excess:.3e}")
    print("ALL ASSERTIONS PASSED!")

if __name__ == "__main__":
    verify_symbolic_certificates()
    verify_full_n500()
