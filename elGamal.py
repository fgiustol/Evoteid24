"""Elliptic Curve ElGamal implementation

This file contains an Elliptic Curve ElGamal implementation,
containing group and key generation, and functions for encryption,
decryption and re-encryption.

The functions in this file are imported and used for the proof related
implementations in other files of this project.

This file requires that the environment you are running on have the 'petlib'
library installed, which comes with an installation of the 'ZKSK' library
needed for the other files in this project.

The file contains the following functions:
    - keygen: returns the group generator, order, and a key pair
    - enc: returns an EC elgamal encrypted ciphertext
    - dec: returns an EC elgamal decrypted message
    - re_enc: returns an EC elgamal re-encrypted ciphertext
"""

from petlib.ec import EcGroup
import petlib.bn
from Polynom import PolynomMod
import functools
import operator

from typing import List

def keygen_threshold(threshold, total):
    group = EcGroup()
    g = group.generator()
    order = group.order()
    h = group.generator()

    sk = order.random()
    pk = sk * g

    #Shamir's Secret Sharing
    polynom = PolynomMod.create_random_polynom(sk, threshold - 1, order)
    supporting_points = range(1, total + 1)
    shares = [(x, polynom.evaluate(x), g, order) for x in supporting_points]

    return g, h, order, pk, shares

def keygen():
    """Generates an EC group, generator, order and key pair

    Args:
        no arguments
    
    Returns:
        g (EcPt): group generator
        order (Bn): group order
        pk (EcPt): public key
        sk (Bn): secret key
    """
    
    #Using the petlib library group operations to generate group
    #and group values
    group = EcGroup()
    g = group.generator()
    order = group.order()

    #Generating secret key at random from the EC group
    sk = order.random()
    pk = sk * g
    
    return (g, order, pk, sk)


def enc(g, pk, m, r):
    """Encryption of a message

    Args:
        g (EcPt): group generator
        pk (EcPt): public key of the receiver
        m (Bn) or (int): message to be encrypted
        r (Bn) : randomness
    
    Returns:
        (c0,c1) (EcPt, EcPt): ciphertext of encrypted message (c0, c1),
                              where c0 = r*g and c1 = m*g + r*pk
    """
    
    #Elliptic Curve so g**m * pk**r becomes m*g + r*pk
    c0 = r*g
    c1 = m*g + r*pk

    return (c0, c1)


def partial_dec(key_share, encryption):
    yC1 =  key_share[1] * encryption[0] 
    return key_share[0], yC1

def ecc_sum(points: List):
    """ Compute the sum of a list of EccPoints. """
    if len(points) == 0:
        return None
    elif len(points) == 1:
        return points[0]
    else:
        result = points[0]
        for point in points[1:]:
            result += point
        return result

def full_dec(partial_decryptions, enc_m, q):
    partial_indices = [dec[0] for dec in partial_decryptions]
    lagrange_coefficients = [lagrange_coefficient_for_key_share_indices(partial_indices, idx, q) for idx in partial_indices]
    summands = [lagrange_coefficients[i][2] * partial_decryptions[i][1] for i in range(0, len(partial_decryptions))]
    restored_kdP = ecc_sum(summands)
    return enc_m[1] + (-restored_kdP)

def lagrange_coefficient_for_key_share_indices(key_share_indices: List,
                                               p_idx: int,
                                               order):
    """
    Create the ith Lagrange coefficient for a list of key shares.

    :param key_share_indices: the used indices for the participants key shares
    :param curve_params: the used curve parameters
    :param p_idx: the participant index (= the shares x value), the Lagrange coefficient belongs to
    :return:
    """

    idx_len = len(key_share_indices)
    i = key_share_indices.index(p_idx)

    def x(idx):
        return key_share_indices[idx]

    def prod(factors: List[int]) -> int:
        """ Compute the product of a list of integers. """
        return functools.reduce(operator.mul, factors, 1)

    tmp = [(- x(j) * petlib.bn.Bn(x(i) - x(j)).mod_inverse(order)) for j in range(0, idx_len) if not j == i]
    coefficient = prod(tmp) % order  # lambda_i

    return p_idx, key_share_indices, coefficient


def dec(ct, sk):
    """Decryption of a ciphertext

    Args:
        ct (EcPt, EcPt): ciphertext of encrypted message (c0, c1),
                        where c0 = r*g and c1 = m*g + r*pk
        sk (Bn): secret key / decryption key
    
    Returns:
        message (EcPt): decrypted message, m, on the form m*g
    """

    c0, c1 = ct

    message = (c1 + (-sk*c0))

    return message



def re_enc(g, pk, ct, r):
    """Re-Encryption of a ciphertext

    Args:
        g (EcPt): group generator
        pk (EcPt): public key of the receiver
        ct (EcPt, EcPt): ciphertext of encrypted message (c0, c1),
                         where c0 = r*g and c1 = m*g + r*pk
        r (Bn): randomness
    
    Returns:
        (c0Prime, c1Prime) (EcPt, EcPt): ciphertext (c0Prime, c1Prime)
                                         of re-encrypted ciphertext (c0, c1),
                                         where c0 = r*g and c1 = m*g + r*pk and,
                                         c0Prime = c0 + r*g and c1Prime = c1 + r*pk
    """
    
    c0, c1 = ct

    c0Prime = c0 + r*g
    c1Prime = c1 + r*pk

    return (c0Prime, c1Prime)

def prod_enc(ct1, CT2):

    c0Prime = ct1[0]
    c1Prime = ct1[1]

    for ct2 in CT2:
        c0Prime += ct2[0]
        c1Prime += ct2[1]

    return (c0Prime, c1Prime)

