// Project 2 - Implementation and breaking of RSA cipher
// Cryptography
// Nikola Valesova, xvales02


#include <iostream>
#include <gmpxx.h>
#include <string>
#include <time.h>
#include "kry.h"

using namespace std;


// Miller–Rabin primality test
bool millerTest(mpz_t d, mpz_t n, gmp_randstate_t state) {
    mpz_t a, tmp, x;
    mpz_inits(a, tmp, x, NULL);

    // tmp <- n - 4
    mpz_sub_ui(tmp, n, 4);
    mpz_urandomm(a, state, tmp);
    mpz_add_ui(a, a, 2);

    // x <- a^d % n
    mpz_powm(x, a, d, n);

    mpz_sub_ui(tmp, n, 1);
    if (mpz_cmp_ui(x, 1) == 0 || mpz_cmp(x, tmp) == 0) {
        mpz_clears(a, tmp, x, NULL);
        return true;
    }

    while (mpz_cmp(d, tmp) != 0) {
        // x <- (x * x) % n;
        mpz_mul(x, x, x);
        mpz_mod(x, x, n);
        // d <- d * 2
        mpz_mul_ui(d, d, 2);

        if (mpz_cmp_ui(x, 1) == 0) {
            mpz_clears(a, tmp, x, NULL);
            return false;
        }
        if (mpz_cmp(x, tmp) == 0) {
            mpz_clears(a, tmp, x, NULL);
            return true;
        }
    }

    mpz_clears(a, tmp, x, NULL);
    return false;
}


// return false if prime is composite, return true if prime is probably prime
bool isPrime(mpz_t prime, int k, gmp_randstate_t state) {
    if (mpz_cmp_ui(prime, 1) <= 0 || mpz_cmp_ui(prime, 4) == 0)
        return false;
    if (mpz_cmp_ui(prime, 3) <= 0)
        return true;

    // d <- prime - 1
    mpz_t d, tmp;
    mpz_init_set(d, prime);
    mpz_sub_ui(d, d, 1);
    // tmp <- d % 2
    mpz_init(tmp);
    mpz_mod_ui(tmp, d, 2);

    while (mpz_cmp_ui(tmp, 0) == 0) {
        mpz_div_ui(d, d, 2);
        mpz_mod_ui(tmp, d, 2);
    }

    // iterate given nuber of 'k' times
    for (int i = 0; i < k; i++) {
        if (!millerTest(d, prime, state)) {
            mpz_clears(d, tmp, NULL);
            return false;
        }
    }

    mpz_clears(d, tmp, NULL);
    return true;
}


// return c as the greatest common divisor of a and b
void GCD(mpz_t a, mpz_t b, mpz_t c) {
    mpz_t a_copy, b_copy;
    mpz_init_set(a_copy, a);
    mpz_init_set(b_copy, b);

    while (mpz_cmp_ui(a_copy, 0)) {
        mpz_set(c, a_copy);
        mpz_mod(a_copy, b_copy, a_copy);
        mpz_set(b_copy, c);
    }

    mpz_clears(a_copy, b_copy, NULL);
}


// return d as a multiplicative inverse of e in modulo phi
void multInverse(mpz_t e, mpz_t phi, mpz_t d) {
    mpz_t x, e_copy, phi_copy, tmp, b0, t, q, x0, x1;
    mpz_inits(x, tmp, b0, t, q, x0, x1, NULL);
    mpz_init_set(e_copy, e);
    mpz_init_set(phi_copy, phi);

    mpz_set(b0, phi);
    mpz_set_ui(x0, 0);
    mpz_set_ui(x1, 1);
    if (mpz_cmp_ui(phi, 1) == 0) {
        mpz_set_ui(d, 1);
        mpz_clears(x, e_copy, phi_copy, tmp, b0, t, q, x0, x1, NULL);
        return;
    }
    while (mpz_cmp_ui(e_copy, 1) > 0) {
        mpz_div(q, e_copy, phi_copy);
        mpz_set(t, phi_copy);
        mpz_mod(phi_copy, e_copy, phi_copy);
        mpz_set(e_copy, t);
        mpz_set(t, x0);
        mpz_mul(tmp, q, x0);
        mpz_sub(x0, x1, tmp);
        mpz_set(x1, t);
    }
    if (mpz_cmp_ui(x1, 0) < 0)
        mpz_add(x1, x1, b0);
    mpz_set(d, x1);
    mpz_clears(x, e_copy, phi_copy, tmp, b0, t, q, x0, x1, NULL);
    return;
}


// generate a random prime number
void getRandomPrime(mpz_t prime, mp_bitcnt_t bitCount, gmp_randstate_t state) {
    mpz_t tmp;
    mpz_init(tmp);

    while (true) {
        mpz_urandomb(prime, state, bitCount);
        if (isPrime(prime, 10, state))
            break;
    }

    mpz_clear(tmp);
}


// compute random prime numbers p and q and public modulus n
void getPQN(mpz_t p, mpz_t q, mpz_t n, mp_bitcnt_t bitCount, gmp_randstate_t state) {
    mpz_t tmp, MSB;
    mpz_inits(tmp, MSB, NULL);
    mpz_set_ui(MSB, 1 << (bitCount - 1));

    while (true) {
        getRandomPrime(p, bitCount / 2, state);
        getRandomPrime(q, bitCount - mpz_sizeinbase(p, 2), state);
        // n = p * q
        mpz_mul(n, p, q);
        mpz_and(tmp, n, MSB);
        if (mpz_cmp_ui(tmp, 0) != 0)
            break;
    }

    mpz_clears(tmp, MSB, NULL);
}


// compute public exponent e and coeficient phi
void getEPhi(mpz_t e, mpz_t phi, mpz_t p, mpz_t q, gmp_randstate_t state) {
    mpz_t p1, q1, tmp;
    mpz_inits(p1, q1, tmp, NULL);

    // phi = (p - 1) * (q - 1)
    mpz_sub_ui(p1, p, 1);
    mpz_sub_ui(q1, q, 1);
    mpz_mul(phi, p1, q1);
    // choose e in range (1, phi), so that gcd(e, phi) == 1
    while (true) {
        mpz_urandomm(e, state, phi);
        mpz_add_ui(e, e, 1);
        GCD(e, phi, tmp);
        if (mpz_cmp_ui(tmp, 1) == 0)
            break;
    }

    mpz_clears(p1, q1, tmp, NULL);
}


// generate public and private keys of RSA
void generateKeys(mp_bitcnt_t bitCount) {
    mpz_t p, q, n, phi, e, d;
    mpz_inits(p, q, n, phi, e, d, NULL);
    gmp_randstate_t state;
    gmp_randinit_default(state);
    // unsigned long int seed = 15879465465;
    // gmp_randseed_ui(state, seed);
    gmp_randseed_ui(state, time(NULL));

    getPQN(p, q, n, bitCount, state);
    getEPhi(e, phi, p, q, state);
    multInverse(e, phi, d);

    cout << hex << showbase << p << " " << q << " " << n << " " << e << " " << d << endl;
    mpz_clears(p, q, n, phi, e, d, NULL);
    gmp_randclear(state);
}


// encrypt/decrypt message text using key consisting of exponent and modulus
void encryption(mpz_t exponent, mpz_t modulus, mpz_t text) {
    mpz_t result;
    mpz_init(result);

    mpz_powm(result, text, exponent, modulus);

    cout << hex << showbase << result << endl;
    mpz_clear(result);
}


// trivial division by the first 1 000 000 numbers
bool trivialDivisionSuccess(mpz_t modulus) {
    unsigned int idx = 0;
    mpz_t i, rest;
    mpz_inits(i, rest, NULL);

    for (mpz_set_ui(i, primeNumbers[idx++]); idx < primesCount; mpz_set_ui(i, primeNumbers[idx++])) {
        mpz_mod(rest, modulus, i);
        if (mpz_cmp_ui(rest, 0) == 0 && mpz_cmp(modulus, i) != 0) {
            cout << hex << showbase << i << endl;
            mpz_clears(i, rest, NULL);
            return true;
        }
    }
    return false;
}


// auxiliary function g(x) = (x^2 + 1) mod modulus
void g(mpz_t x, mpz_t modulus) {
    mpz_mul(x, x, x);
    mpz_add_ui(x, x, 1);
    mpz_mod(x, x, modulus);
}


// Pollard Rho factorization method
void PollardRho(mpz_t modulus) {
    mpz_t x, y, d;

    // x = 2; y = 2; d = 1
    mpz_init_set_ui(x, 2);
    mpz_init_set_ui(y, 2);
    mpz_init_set_ui(d, 1);

    // while d == 1
    while (mpz_cmp_ui(d, 1) == 0) {
        // x <- g(x)
        g(x, modulus);
        // y <- g(g(y))
        g(y, modulus);
        g(y, modulus);
        // d <- gcd(|x - y|, n)
        mpz_sub(d, x, y);
        mpz_abs(d, d);
        GCD(d, modulus, d);
    }
    if (mpz_cmp(d, modulus) == 0)
        cerr << "ERROR: No factors found!";
    else
        cout << hex << showbase << d << endl;

    mpz_clears(x, y, d, NULL);
}


// break public modulus of RSA key
int breakRSA(mpz_t modulus) {
    gmp_randstate_t state;
    gmp_randinit_default(state);
    gmp_randseed_ui(state, time(NULL));

    // check if modulus is not prime
    if (isPrime(modulus, 10, state)) {
        cerr << "ERROR: Modulus is a prime number, has no factors!" << endl;
        gmp_randclear(state);
        return 1;
    }
    gmp_randclear(state);

    if (!trivialDivisionSuccess(modulus))
        PollardRho(modulus);

    return 0;
}


// MAIN
int main(int argc, char *argv[]) {
    string operation = argv[1];

    // generate key
    if (operation == "-g" && argc == 3) {
        mp_bitcnt_t bitCount = strtoul(argv[2], NULL, 10);
        generateKeys(bitCount);
    }
    // encrypt/decrypt
    else if ((operation == "-e" || operation == "-d") && argc == 5) {
        mpz_t exponent, modulus, text;
        mpz_init_set_str(exponent, argv[2] + 2, 16);
        mpz_init_set_str(modulus, argv[3] + 2, 16);
        mpz_init_set_str(text, argv[4] + 2, 16);

        encryption(exponent, modulus, text);

        mpz_clears(exponent, modulus, text, NULL);
    }
    // break RSA cipher
    else if (operation == "-b" && argc == 3) {
        mpz_t modulus;
        mpz_init_set_str(modulus, argv[2] + 2, 16);
        int retval = breakRSA(modulus);
        mpz_clear(modulus);
        return retval;
    }
    else {
        cerr << "ERROR: Invalid input parameters!" << endl;
        return 1;
    }

    return 0;
}
