// SPDX-License-Identifier: MIT

pragma solidity ^0.8.0;

import {IVerifier} from "./IVerifier.sol";

contract Halo2Verifier is IVerifier {
    uint256 internal constant DELTA =
        4131629893567559867359510883348571134090853742863529169391034518566172092834;
    uint256 internal constant R =
        21888242871839275222246405745257275088548364400416034343698204186575808495617;
    uint256 internal constant PROOF_LEN_CPTR = 0x6014f51944;
    uint256 internal constant PROOF_CPTR = 0x64;
    uint256 internal constant NUM_INSTANCE_CPTR = 0x1244;
    uint256 internal constant INSTANCE_CPTR = 0x1264;

    uint256 internal constant FIRST_QUOTIENT_X_CPTR = 0x07a4;
    uint256 internal constant LAST_QUOTIENT_X_CPTR = 0x08a4;

    uint256 internal constant VK_MPTR = 0x05a0;
    uint256 internal constant VK_DIGEST_MPTR = 0x05a0;
    uint256 internal constant NUM_INSTANCES_MPTR = 0x05c0;
    uint256 internal constant K_MPTR = 0x05e0;
    uint256 internal constant N_INV_MPTR = 0x0600;
    uint256 internal constant OMEGA_MPTR = 0x0620;
    uint256 internal constant OMEGA_INV_MPTR = 0x0640;
    uint256 internal constant OMEGA_INV_TO_L_MPTR = 0x0660;
    uint256 internal constant HAS_ACCUMULATOR_MPTR = 0x0680;
    uint256 internal constant ACC_OFFSET_MPTR = 0x06a0;
    uint256 internal constant NUM_ACC_LIMBS_MPTR = 0x06c0;
    uint256 internal constant NUM_ACC_LIMB_BITS_MPTR = 0x06e0;
    uint256 internal constant G1_X_MPTR = 0x0700;
    uint256 internal constant G1_Y_MPTR = 0x0720;
    uint256 internal constant G2_X_1_MPTR = 0x0740;
    uint256 internal constant G2_X_2_MPTR = 0x0760;
    uint256 internal constant G2_Y_1_MPTR = 0x0780;
    uint256 internal constant G2_Y_2_MPTR = 0x07a0;
    uint256 internal constant NEG_S_G2_X_1_MPTR = 0x07c0;
    uint256 internal constant NEG_S_G2_X_2_MPTR = 0x07e0;
    uint256 internal constant NEG_S_G2_Y_1_MPTR = 0x0800;
    uint256 internal constant NEG_S_G2_Y_2_MPTR = 0x0820;

    uint256 internal constant CHALLENGE_MPTR = 0x0f40;

    uint256 internal constant THETA_MPTR = 0x0f40;
    uint256 internal constant BETA_MPTR = 0x0f60;
    uint256 internal constant GAMMA_MPTR = 0x0f80;
    uint256 internal constant Y_MPTR = 0x0fa0;
    uint256 internal constant X_MPTR = 0x0fc0;
    uint256 internal constant ZETA_MPTR = 0x0fe0;
    uint256 internal constant NU_MPTR = 0x1000;
    uint256 internal constant MU_MPTR = 0x1020;

    uint256 internal constant ACC_LHS_X_MPTR = 0x1040;
    uint256 internal constant ACC_LHS_Y_MPTR = 0x1060;
    uint256 internal constant ACC_RHS_X_MPTR = 0x1080;
    uint256 internal constant ACC_RHS_Y_MPTR = 0x10a0;
    uint256 internal constant X_N_MPTR = 0x10c0;
    uint256 internal constant X_N_MINUS_1_INV_MPTR = 0x10e0;
    uint256 internal constant L_LAST_MPTR = 0x1100;
    uint256 internal constant L_BLIND_MPTR = 0x1120;
    uint256 internal constant L_0_MPTR = 0x1140;
    uint256 internal constant INSTANCE_EVAL_MPTR = 0x1160;
    uint256 internal constant QUOTIENT_EVAL_MPTR = 0x1180;
    uint256 internal constant QUOTIENT_X_MPTR = 0x11a0;
    uint256 internal constant QUOTIENT_Y_MPTR = 0x11c0;
    uint256 internal constant R_EVAL_MPTR = 0x11e0;
    uint256 internal constant PAIRING_LHS_X_MPTR = 0x1200;
    uint256 internal constant PAIRING_LHS_Y_MPTR = 0x1220;
    uint256 internal constant PAIRING_RHS_X_MPTR = 0x1240;
    uint256 internal constant PAIRING_RHS_Y_MPTR = 0x1260;

    function verifyProof(
        bytes calldata proof,
        uint256[] calldata instances
    ) public returns (bool) {
        assembly {
            // Read EC point (x, y) at (proof_cptr, proof_cptr + 0x20),
            // and check if the point is on affine plane,
            // and store them in (hash_mptr, hash_mptr + 0x20).
            // Return updated (success, proof_cptr, hash_mptr).
            function read_ec_point(success, proof_cptr, hash_mptr, q)
                -> ret0, ret1, ret2
            {
                let x := calldataload(proof_cptr)
                let y := calldataload(add(proof_cptr, 0x20))
                ret0 := and(success, lt(x, q))
                ret0 := and(ret0, lt(y, q))
                ret0 := and(
                    ret0,
                    eq(
                        mulmod(y, y, q),
                        addmod(mulmod(x, mulmod(x, x, q), q), 3, q)
                    )
                )
                mstore(hash_mptr, x)
                mstore(add(hash_mptr, 0x20), y)
                ret1 := add(proof_cptr, 0x40)
                ret2 := add(hash_mptr, 0x40)
            }

            // Squeeze challenge by keccak256(memory[0..hash_mptr]),
            // and store hash mod r as challenge in challenge_mptr,
            // and push back hash in 0x00 as the first input for next squeeze.
            // Return updated (challenge_mptr, hash_mptr).
            function squeeze_challenge(challenge_mptr, hash_mptr, r)
                -> ret0, ret1
            {
                let hash := keccak256(0x00, hash_mptr)
                mstore(challenge_mptr, mod(hash, r))
                mstore(0x00, hash)
                ret0 := add(challenge_mptr, 0x20)
                ret1 := 0x20
            }

            // Squeeze challenge without absorbing new input from calldata,
            // by putting an extra 0x01 in memory[0x20] and squeeze by keccak256(memory[0..21]),
            // and store hash mod r as challenge in challenge_mptr,
            // and push back hash in 0x00 as the first input for next squeeze.
            // Return updated (challenge_mptr).
            function squeeze_challenge_cont(challenge_mptr, r) -> ret {
                mstore8(0x20, 0x01)
                let hash := keccak256(0x00, 0x21)
                mstore(challenge_mptr, mod(hash, r))
                mstore(0x00, hash)
                ret := add(challenge_mptr, 0x20)
            }

            // Batch invert values in memory[mptr_start..mptr_end] in place.
            // Return updated (success).
            function batch_invert(success, mptr_start, mptr_end) -> ret {
                let gp_mptr := mptr_end
                let gp := mload(mptr_start)
                let mptr := add(mptr_start, 0x20)
                for {

                } lt(mptr, sub(mptr_end, 0x20)) {

                } {
                    gp := mulmod(gp, mload(mptr), R)
                    mstore(gp_mptr, gp)
                    mptr := add(mptr, 0x20)
                    gp_mptr := add(gp_mptr, 0x20)
                }
                gp := mulmod(gp, mload(mptr), R)

                mstore(gp_mptr, 0x20)
                mstore(add(gp_mptr, 0x20), 0x20)
                mstore(add(gp_mptr, 0x40), 0x20)
                mstore(add(gp_mptr, 0x60), gp)
                mstore(add(gp_mptr, 0x80), sub(R, 2))
                mstore(add(gp_mptr, 0xa0), R)
                ret := and(
                    success,
                    staticcall(gas(), 0x05, gp_mptr, 0xc0, gp_mptr, 0x20)
                )
                let all_inv := mload(gp_mptr)

                let first_mptr := mptr_start
                let second_mptr := add(first_mptr, 0x20)
                gp_mptr := sub(gp_mptr, 0x20)
                for {

                } lt(second_mptr, mptr) {

                } {
                    let inv := mulmod(all_inv, mload(gp_mptr), R)
                    all_inv := mulmod(all_inv, mload(mptr), R)
                    mstore(mptr, inv)
                    mptr := sub(mptr, 0x20)
                    gp_mptr := sub(gp_mptr, 0x20)
                }
                let inv_first := mulmod(all_inv, mload(second_mptr), R)
                let inv_second := mulmod(all_inv, mload(first_mptr), R)
                mstore(first_mptr, inv_first)
                mstore(second_mptr, inv_second)
            }

            // Add (x, y) into point at (0x00, 0x20).
            // Return updated (success).
            function ec_add_acc(success, x, y) -> ret {
                mstore(0x40, x)
                mstore(0x60, y)
                ret := and(
                    success,
                    staticcall(gas(), 0x06, 0x00, 0x80, 0x00, 0x40)
                )
            }

            // Scale point at (0x00, 0x20) by scalar.
            function ec_mul_acc(success, scalar) -> ret {
                mstore(0x40, scalar)
                ret := and(
                    success,
                    staticcall(gas(), 0x07, 0x00, 0x60, 0x00, 0x40)
                )
            }

            // Add (x, y) into point at (0x80, 0xa0).
            // Return updated (success).
            function ec_add_tmp(success, x, y) -> ret {
                mstore(0xc0, x)
                mstore(0xe0, y)
                ret := and(
                    success,
                    staticcall(gas(), 0x06, 0x80, 0x80, 0x80, 0x40)
                )
            }

            // Scale point at (0x80, 0xa0) by scalar.
            // Return updated (success).
            function ec_mul_tmp(success, scalar) -> ret {
                mstore(0xc0, scalar)
                ret := and(
                    success,
                    staticcall(gas(), 0x07, 0x80, 0x60, 0x80, 0x40)
                )
            }

            // Perform pairing check.
            // Return updated (success).
            function ec_pairing(success, lhs_x, lhs_y, rhs_x, rhs_y) -> ret {
                mstore(0x00, lhs_x)
                mstore(0x20, lhs_y)
                mstore(0x40, mload(G2_X_1_MPTR))
                mstore(0x60, mload(G2_X_2_MPTR))
                mstore(0x80, mload(G2_Y_1_MPTR))
                mstore(0xa0, mload(G2_Y_2_MPTR))
                mstore(0xc0, rhs_x)
                mstore(0xe0, rhs_y)
                mstore(0x100, mload(NEG_S_G2_X_1_MPTR))
                mstore(0x120, mload(NEG_S_G2_X_2_MPTR))
                mstore(0x140, mload(NEG_S_G2_Y_1_MPTR))
                mstore(0x160, mload(NEG_S_G2_Y_2_MPTR))
                ret := and(
                    success,
                    staticcall(gas(), 0x08, 0x00, 0x180, 0x00, 0x20)
                )
                ret := and(ret, mload(0x00))
            }

            // Modulus
            let
                q
            := 21888242871839275222246405745257275088696311157297823662689037894645226208583 // BN254 base field
            let
                r
            := 21888242871839275222246405745257275088548364400416034343698204186575808495617 // BN254 scalar field

            // Initialize success as true
            let success := true

            {
                // Load vk_digest and num_instances of vk into memory
                mstore(
                    0x05a0,
                    0x16617609256c0196d6e38792485b3bb7b944504429b0723bb8f177d491e38e9d
                ) // vk_digest
                mstore(
                    0x05c0,
                    0x0000000000000000000000000000000000000000000000000000000000000005
                ) // num_instances

                // Check valid length of proof
                success := and(
                    success,
                    eq(0x11e0, calldataload(sub(PROOF_LEN_CPTR, 0x6014F51900)))
                )

                // Check valid length of instances
                let num_instances := mload(NUM_INSTANCES_MPTR)
                success := and(
                    success,
                    eq(num_instances, calldataload(NUM_INSTANCE_CPTR))
                )

                // Absorb vk diegst
                mstore(0x00, mload(VK_DIGEST_MPTR))

                // Read instances and witness commitments and generate challenges
                let hash_mptr := 0x20
                let instance_cptr := INSTANCE_CPTR
                for {
                    let instance_cptr_end := add(
                        instance_cptr,
                        mul(0x20, num_instances)
                    )
                } lt(instance_cptr, instance_cptr_end) {

                } {
                    let instance := calldataload(instance_cptr)
                    success := and(success, lt(instance, r))
                    mstore(hash_mptr, instance)
                    instance_cptr := add(instance_cptr, 0x20)
                    hash_mptr := add(hash_mptr, 0x20)
                }

                let proof_cptr := PROOF_CPTR
                let challenge_mptr := CHALLENGE_MPTR

                // Phase 1
                for {
                    let proof_cptr_end := add(proof_cptr, 0x0240)
                } lt(proof_cptr, proof_cptr_end) {

                } {
                    success, proof_cptr, hash_mptr := read_ec_point(
                        success,
                        proof_cptr,
                        hash_mptr,
                        q
                    )
                }

                challenge_mptr, hash_mptr := squeeze_challenge(
                    challenge_mptr,
                    hash_mptr,
                    r
                )

                // Phase 2
                for {
                    let proof_cptr_end := add(proof_cptr, 0x0200)
                } lt(proof_cptr, proof_cptr_end) {

                } {
                    success, proof_cptr, hash_mptr := read_ec_point(
                        success,
                        proof_cptr,
                        hash_mptr,
                        q
                    )
                }

                challenge_mptr, hash_mptr := squeeze_challenge(
                    challenge_mptr,
                    hash_mptr,
                    r
                )
                challenge_mptr := squeeze_challenge_cont(challenge_mptr, r)

                // Phase 3
                for {
                    let proof_cptr_end := add(proof_cptr, 0x0300)
                } lt(proof_cptr, proof_cptr_end) {

                } {
                    success, proof_cptr, hash_mptr := read_ec_point(
                        success,
                        proof_cptr,
                        hash_mptr,
                        q
                    )
                }

                challenge_mptr, hash_mptr := squeeze_challenge(
                    challenge_mptr,
                    hash_mptr,
                    r
                )

                // Phase 4
                for {
                    let proof_cptr_end := add(proof_cptr, 0x0140)
                } lt(proof_cptr, proof_cptr_end) {

                } {
                    success, proof_cptr, hash_mptr := read_ec_point(
                        success,
                        proof_cptr,
                        hash_mptr,
                        q
                    )
                }

                challenge_mptr, hash_mptr := squeeze_challenge(
                    challenge_mptr,
                    hash_mptr,
                    r
                )

                // Read evaluations
                for {
                    let proof_cptr_end := add(proof_cptr, 0x08e0)
                } lt(proof_cptr, proof_cptr_end) {

                } {
                    let eval := calldataload(proof_cptr)
                    success := and(success, lt(eval, r))
                    mstore(hash_mptr, eval)
                    proof_cptr := add(proof_cptr, 0x20)
                    hash_mptr := add(hash_mptr, 0x20)
                }

                // Read batch opening proof and generate challenges
                challenge_mptr, hash_mptr := squeeze_challenge(
                    challenge_mptr,
                    hash_mptr,
                    r
                ) // zeta
                challenge_mptr := squeeze_challenge_cont(challenge_mptr, r) // nu

                success, proof_cptr, hash_mptr := read_ec_point(
                    success,
                    proof_cptr,
                    hash_mptr,
                    q
                ) // W

                challenge_mptr, hash_mptr := squeeze_challenge(
                    challenge_mptr,
                    hash_mptr,
                    r
                ) // mu

                success, proof_cptr, hash_mptr := read_ec_point(
                    success,
                    proof_cptr,
                    hash_mptr,
                    q
                ) // W'

                // Load full vk into memory
                mstore(
                    0x05a0,
                    0x16617609256c0196d6e38792485b3bb7b944504429b0723bb8f177d491e38e9d
                ) // vk_digest
                mstore(
                    0x05c0,
                    0x0000000000000000000000000000000000000000000000000000000000000005
                ) // num_instances
                mstore(
                    0x05e0,
                    0x0000000000000000000000000000000000000000000000000000000000000007
                ) // k
                mstore(
                    0x0600,
                    0x300385d5fb6f3ce964dfa52b147e55ac6de38077e8c5fdb0215a31a8c8200001
                ) // n_inv
                mstore(
                    0x0620,
                    0x2822ef9d2d155c2b49f7a010aeec0dae3df9cff80535c8d08c9e954b942e6d6b
                ) // omega
                mstore(
                    0x0640,
                    0x1e3cef5e680760be385354b20cfa424b1545b57ee133143343ec8178b2e4ae8b
                ) // omega_inv
                mstore(
                    0x0660,
                    0x2f0215559e251f1423df018c84fc874f074743154e03a1f96e57c953a337654c
                ) // omega_inv_to_l
                mstore(
                    0x0680,
                    0x0000000000000000000000000000000000000000000000000000000000000000
                ) // has_accumulator
                mstore(
                    0x06a0,
                    0x0000000000000000000000000000000000000000000000000000000000000000
                ) // acc_offset
                mstore(
                    0x06c0,
                    0x0000000000000000000000000000000000000000000000000000000000000000
                ) // num_acc_limbs
                mstore(
                    0x06e0,
                    0x0000000000000000000000000000000000000000000000000000000000000000
                ) // num_acc_limb_bits
                mstore(
                    0x0700,
                    0x0000000000000000000000000000000000000000000000000000000000000001
                ) // g1_x
                mstore(
                    0x0720,
                    0x0000000000000000000000000000000000000000000000000000000000000002
                ) // g1_y
                mstore(
                    0x0740,
                    0x198e9393920d483a7260bfb731fb5d25f1aa493335a9e71297e485b7aef312c2
                ) // g2_x_1
                mstore(
                    0x0760,
                    0x1800deef121f1e76426a00665e5c4479674322d4f75edadd46debd5cd992f6ed
                ) // g2_x_2
                mstore(
                    0x0780,
                    0x090689d0585ff075ec9e99ad690c3395bc4b313370b38ef355acdadcd122975b
                ) // g2_y_1
                mstore(
                    0x07a0,
                    0x12c85ea5db8c6deb4aab71808dcb408fe3d1e7690c43d37b4ce6cc0166fa7daa
                ) // g2_y_2
                mstore(
                    0x07c0,
                    0x186282957db913abd99f91db59fe69922e95040603ef44c0bd7aa3adeef8f5ac
                ) // neg_s_g2_x_1
                mstore(
                    0x07e0,
                    0x17944351223333f260ddc3b4af45191b856689eda9eab5cbcddbbe570ce860d2
                ) // neg_s_g2_x_2
                mstore(
                    0x0800,
                    0x06d971ff4a7467c3ec596ed6efc674572e32fd6f52b721f97e35b0b3d3546753
                ) // neg_s_g2_y_1
                mstore(
                    0x0820,
                    0x06ecdb9f9567f59ed2eee36e1e1d58797fd13cc97fafc2910f5e8a12f202fa9a
                ) // neg_s_g2_y_2
                mstore(
                    0x0840,
                    0x2712de3615a6cb81ddbd74628e923f4feb758583c854a09599d026b515ca2c48
                ) // fixed_comms[0].x
                mstore(
                    0x0860,
                    0x19cfcf54133241843db078b7db1e33633ab0adc950308f97a254bbb38009ed40
                ) // fixed_comms[0].y
                mstore(
                    0x0880,
                    0x1e103d76f2587a1fab3f81cc7a702abcb5b84ddd2aac8289d0fa359b2bc31c5d
                ) // fixed_comms[1].x
                mstore(
                    0x08a0,
                    0x20238d78134d3905b909107c5e9a0a37ce614d86f5bc551f76d08cfe738892c6
                ) // fixed_comms[1].y
                mstore(
                    0x08c0,
                    0x1a36f8669926fd9ec228372f38d32989449a2fa49c997cfd9fa6ea1b3bf86bcf
                ) // fixed_comms[2].x
                mstore(
                    0x08e0,
                    0x123563f1c84a45a44b5100c40c6ee11cecb97d80a905f33410736b19523af8c8
                ) // fixed_comms[2].y
                mstore(
                    0x0900,
                    0x18290cb8da3c4ceb8ff25041dca3e29c600f5e0201457cd935c8c81dc5fff6dd
                ) // fixed_comms[3].x
                mstore(
                    0x0920,
                    0x1a5e96cc3634cd25b43b106b48cf3efb6627a38fb2c03c196c1d0276737a203e
                ) // fixed_comms[3].y
                mstore(
                    0x0940,
                    0x1335021d399fead50cda0ccb608618228f43b10635f05112c00f89750ab517c6
                ) // fixed_comms[4].x
                mstore(
                    0x0960,
                    0x1798e0be1444dc8ff4794112e6dd0b27518860e931592f73574c86201b86c005
                ) // fixed_comms[4].y
                mstore(
                    0x0980,
                    0x1db033b78f685be7a1e45f3c80d5c45e285d4a6307e8029032a2a69ad52a9f56
                ) // fixed_comms[5].x
                mstore(
                    0x09a0,
                    0x1d544374e403d1e6ebfb5f92873f6b6f57222b42c6f7e44aada01b113568e7a2
                ) // fixed_comms[5].y
                mstore(
                    0x09c0,
                    0x03944f155c54d44a9f716b45a38e713ddda3563b522ac7c1755537e1d4950820
                ) // fixed_comms[6].x
                mstore(
                    0x09e0,
                    0x0e20df30847aa768a9aaac896476a8f8d888c159faa0d8d3c25bb3bddc0534c2
                ) // fixed_comms[6].y
                mstore(
                    0x0a00,
                    0x154446a0310b17fab509186b0a1867e20ed7246aa1dd1d495d4080770ef49735
                ) // fixed_comms[7].x
                mstore(
                    0x0a20,
                    0x1cac4f8a0d77d249eccad63955e940867320bba7d2f6c49c90220213414cf257
                ) // fixed_comms[7].y
                mstore(
                    0x0a40,
                    0x0000000000000000000000000000000000000000000000000000000000000000
                ) // fixed_comms[8].x
                mstore(
                    0x0a60,
                    0x0000000000000000000000000000000000000000000000000000000000000000
                ) // fixed_comms[8].y
                mstore(
                    0x0a80,
                    0x2a3695b148257ad8c35fd795c34f5b0a2477bf6f09a6796e89abe31544646e7a
                ) // fixed_comms[9].x
                mstore(
                    0x0aa0,
                    0x143113b933d3582375c4e4b065b10bf79b957a221f3e8c392258e18c418fb012
                ) // fixed_comms[9].y
                mstore(
                    0x0ac0,
                    0x0076c14f61563b47a0e3f73e98f385fda75a4487528758a2bffdc3ea65b65f96
                ) // fixed_comms[10].x
                mstore(
                    0x0ae0,
                    0x15b6bb9cc010f01752b78b184a227999cbc79d207becd596c374e94fb10e1689
                ) // fixed_comms[10].y
                mstore(
                    0x0b00,
                    0x0bc7a6b45d32feedbc045db6cbc8f5302ee1777be852ce1b4f754e4b99026c18
                ) // fixed_comms[11].x
                mstore(
                    0x0b20,
                    0x223beaff1768f42ac36670bcd385f013db9de95e2245f53b946d0915119d1375
                ) // fixed_comms[11].y
                mstore(
                    0x0b40,
                    0x0bc7a6b45d32feedbc045db6cbc8f5302ee1777be852ce1b4f754e4b99026c18
                ) // fixed_comms[12].x
                mstore(
                    0x0b60,
                    0x223beaff1768f42ac36670bcd385f013db9de95e2245f53b946d0915119d1375
                ) // fixed_comms[12].y
                mstore(
                    0x0b80,
                    0x0b00ed74d6e35e994badbd4d2304fdfdf03cf96f8c942a56611f251fc1bf808b
                ) // fixed_comms[13].x
                mstore(
                    0x0ba0,
                    0x011ae707f39e9a132fb69cf51b294118cc3552feeafc351730331d6bf49ffe41
                ) // fixed_comms[13].y
                mstore(
                    0x0bc0,
                    0x1e13a9342d683571aa023749155036002c8cf578ffec7647ba1e8f7fe702621d
                ) // fixed_comms[14].x
                mstore(
                    0x0be0,
                    0x1d87e48557b4682d96fba306acb848e7eb2dbc020a75ba701d8dd90622a2b300
                ) // fixed_comms[14].y
                mstore(
                    0x0c00,
                    0x1bcae640a3353b7a14a89dfd9f1aee948d6cef46ae68260a6f8a99318e3c0784
                ) // fixed_comms[15].x
                mstore(
                    0x0c20,
                    0x04c631ec0f69ef39ab811868eaf4851b3e0d8682f3c99ab3ac22afd57df59ae1
                ) // fixed_comms[15].y
                mstore(
                    0x0c40,
                    0x0000000000000000000000000000000000000000000000000000000000000000
                ) // fixed_comms[16].x
                mstore(
                    0x0c60,
                    0x0000000000000000000000000000000000000000000000000000000000000000
                ) // fixed_comms[16].y
                mstore(
                    0x0c80,
                    0x1e6c725a97dbaa7a75b1b804fef80a7f87a931f57540bca9907ba5df9c71cd02
                ) // permutation_comms[0].x
                mstore(
                    0x0ca0,
                    0x2c278c3dff9d866b35d736cb50b30726d77926fdf93e71b3265184dfe7bffd31
                ) // permutation_comms[0].y
                mstore(
                    0x0cc0,
                    0x1f9701f1456d02bb1ff104b48c2306b640f8e7c1a1e86ad5867d884b733f3c5f
                ) // permutation_comms[1].x
                mstore(
                    0x0ce0,
                    0x13a10a464782dbcddece818215820a1d2a355d8c8c0a1215f70c56e570383efd
                ) // permutation_comms[1].y
                mstore(
                    0x0d00,
                    0x2c5d92a487044e676830df3399bd25bd39ea6852f3ef726eee18aec0aa7f8f1a
                ) // permutation_comms[2].x
                mstore(
                    0x0d20,
                    0x2ab79a4e034e0be0cf0259896bf1f0707d7e045cd325272dbb9fa5dc7fe880e7
                ) // permutation_comms[2].y
                mstore(
                    0x0d40,
                    0x2a29bf02f00ada0795ed37db58a9a8fd83e154d4c825ba2e2abd2848fa58f753
                ) // permutation_comms[3].x
                mstore(
                    0x0d60,
                    0x204f7c49fa636fefb2e3c7d51803b1f9c61032120eed0cffd5ec6ae04a0f9ac6
                ) // permutation_comms[3].y
                mstore(
                    0x0d80,
                    0x0aab096e5caff3719008931ed51f2edff77e979b2a9253f5c09f965c5733c10e
                ) // permutation_comms[4].x
                mstore(
                    0x0da0,
                    0x2b54a6e52e0a07cc0998a886588382e456e19f5445d254f153fa6f12fda9c6a3
                ) // permutation_comms[4].y
                mstore(
                    0x0dc0,
                    0x152f777ae4f7cdfb2ba26a25868ce0bdf286d47f2856729b3bf5fa6b29b65d74
                ) // permutation_comms[5].x
                mstore(
                    0x0de0,
                    0x2a3e88b90ac8ab8b40a32703342d678bc222e4d8d5d4486cb9279be8cbd506f3
                ) // permutation_comms[5].y
                mstore(
                    0x0e00,
                    0x107586ec965090cffbe89d7eddc4c3c8ad42fd8a10213520c205862e3e878acc
                ) // permutation_comms[6].x
                mstore(
                    0x0e20,
                    0x2155878336cca4706f2c0d31286b190654bc0306794a5c08448360d5efeace5d
                ) // permutation_comms[6].y
                mstore(
                    0x0e40,
                    0x2d332162e030d61ee4fceef4e69057510d9463b90af20c81a62f08111b356d2a
                ) // permutation_comms[7].x
                mstore(
                    0x0e60,
                    0x225ea8bc99e1e2ab72d63f37a3997ea3dd1e4dfbc1e3dc121636f51aa5696506
                ) // permutation_comms[7].y
                mstore(
                    0x0e80,
                    0x2febec533422bf411adcfe49457b8d0d058e5c6480bd8528852d64527501ab97
                ) // permutation_comms[8].x
                mstore(
                    0x0ea0,
                    0x2f7baa3a47500091656d264b4c063ed918337cdcbb5ee495051eb4b2b1e88a8e
                ) // permutation_comms[8].y
                mstore(
                    0x0ec0,
                    0x227c25236c2d8b0798741a25696c288879a21a9162f31b44e47cb2b92906247b
                ) // permutation_comms[9].x
                mstore(
                    0x0ee0,
                    0x2911925dda2e4bc7facbcc09881f271f993d527b2ea9c4dfd136c9584c07d89b
                ) // permutation_comms[9].y
                mstore(
                    0x0f00,
                    0x1f7fb5309157aa52a2bde9496c8319b404c8f6b7d8bd7b6c0829197e0fccf435
                ) // permutation_comms[10].x
                mstore(
                    0x0f20,
                    0x1f742f587ebaa7c4b00449a195ff6a8394ee45dd597fc949325a14aaecf1362b
                ) // permutation_comms[10].y

                // Read accumulator from instances
                if mload(HAS_ACCUMULATOR_MPTR) {
                    let num_limbs := mload(NUM_ACC_LIMBS_MPTR)
                    let num_limb_bits := mload(NUM_ACC_LIMB_BITS_MPTR)

                    let cptr := add(
                        INSTANCE_CPTR,
                        mul(mload(ACC_OFFSET_MPTR), 0x20)
                    )
                    let lhs_y_off := mul(num_limbs, 0x20)
                    let rhs_x_off := mul(lhs_y_off, 2)
                    let rhs_y_off := mul(lhs_y_off, 3)
                    let lhs_x := calldataload(cptr)
                    let lhs_y := calldataload(add(cptr, lhs_y_off))
                    let rhs_x := calldataload(add(cptr, rhs_x_off))
                    let rhs_y := calldataload(add(cptr, rhs_y_off))
                    for {
                        let cptr_end := add(cptr, mul(0x20, num_limbs))
                        let shift := num_limb_bits
                    } lt(cptr, cptr_end) {

                    } {
                        cptr := add(cptr, 0x20)
                        lhs_x := add(lhs_x, shl(shift, calldataload(cptr)))
                        lhs_y := add(
                            lhs_y,
                            shl(shift, calldataload(add(cptr, lhs_y_off)))
                        )
                        rhs_x := add(
                            rhs_x,
                            shl(shift, calldataload(add(cptr, rhs_x_off)))
                        )
                        rhs_y := add(
                            rhs_y,
                            shl(shift, calldataload(add(cptr, rhs_y_off)))
                        )
                        shift := add(shift, num_limb_bits)
                    }

                    success := and(
                        success,
                        eq(
                            mulmod(lhs_y, lhs_y, q),
                            addmod(
                                mulmod(lhs_x, mulmod(lhs_x, lhs_x, q), q),
                                3,
                                q
                            )
                        )
                    )
                    success := and(
                        success,
                        eq(
                            mulmod(rhs_y, rhs_y, q),
                            addmod(
                                mulmod(rhs_x, mulmod(rhs_x, rhs_x, q), q),
                                3,
                                q
                            )
                        )
                    )

                    mstore(ACC_LHS_X_MPTR, lhs_x)
                    mstore(ACC_LHS_Y_MPTR, lhs_y)
                    mstore(ACC_RHS_X_MPTR, rhs_x)
                    mstore(ACC_RHS_Y_MPTR, rhs_y)
                }

                pop(q)
            }

            // Revert earlier if anything from calldata is invalid
            if iszero(success) {
                revert(0, 0)
            }

            // Compute lagrange evaluations and instance evaluation
            {
                let k := mload(K_MPTR)
                let x := mload(X_MPTR)
                let x_n := x
                for {
                    let idx := 0
                } lt(idx, k) {
                    idx := add(idx, 1)
                } {
                    x_n := mulmod(x_n, x_n, r)
                }

                let omega := mload(OMEGA_MPTR)

                let mptr := X_N_MPTR
                let mptr_end := add(
                    mptr,
                    mul(0x20, add(mload(NUM_INSTANCES_MPTR), 6))
                )
                if iszero(mload(NUM_INSTANCES_MPTR)) {
                    mptr_end := add(mptr_end, 0x20)
                }
                for {
                    let pow_of_omega := mload(OMEGA_INV_TO_L_MPTR)
                } lt(mptr, mptr_end) {
                    mptr := add(mptr, 0x20)
                } {
                    mstore(mptr, addmod(x, sub(r, pow_of_omega), r))
                    pow_of_omega := mulmod(pow_of_omega, omega, r)
                }
                let x_n_minus_1 := addmod(x_n, sub(r, 1), r)
                mstore(mptr_end, x_n_minus_1)
                success := batch_invert(success, X_N_MPTR, add(mptr_end, 0x20))

                mptr := X_N_MPTR
                let l_i_common := mulmod(x_n_minus_1, mload(N_INV_MPTR), r)
                for {
                    let pow_of_omega := mload(OMEGA_INV_TO_L_MPTR)
                } lt(mptr, mptr_end) {
                    mptr := add(mptr, 0x20)
                } {
                    mstore(
                        mptr,
                        mulmod(
                            l_i_common,
                            mulmod(mload(mptr), pow_of_omega, r),
                            r
                        )
                    )
                    pow_of_omega := mulmod(pow_of_omega, omega, r)
                }

                let l_blind := mload(add(X_N_MPTR, 0x20))
                let l_i_cptr := add(X_N_MPTR, 0x40)
                for {
                    let l_i_cptr_end := add(X_N_MPTR, 0xc0)
                } lt(l_i_cptr, l_i_cptr_end) {
                    l_i_cptr := add(l_i_cptr, 0x20)
                } {
                    l_blind := addmod(l_blind, mload(l_i_cptr), r)
                }

                let instance_eval := 0
                for {
                    let instance_cptr := INSTANCE_CPTR
                    let instance_cptr_end := add(
                        instance_cptr,
                        mul(0x20, mload(NUM_INSTANCES_MPTR))
                    )
                } lt(instance_cptr, instance_cptr_end) {
                    instance_cptr := add(instance_cptr, 0x20)
                    l_i_cptr := add(l_i_cptr, 0x20)
                } {
                    instance_eval := addmod(
                        instance_eval,
                        mulmod(mload(l_i_cptr), calldataload(instance_cptr), r),
                        r
                    )
                }

                let x_n_minus_1_inv := mload(mptr_end)
                let l_last := mload(X_N_MPTR)
                let l_0 := mload(add(X_N_MPTR, 0xc0))

                mstore(X_N_MPTR, x_n)
                mstore(X_N_MINUS_1_INV_MPTR, x_n_minus_1_inv)
                mstore(L_LAST_MPTR, l_last)
                mstore(L_BLIND_MPTR, l_blind)
                mstore(L_0_MPTR, l_0)
                mstore(INSTANCE_EVAL_MPTR, instance_eval)
            }

            // Compute quotient evavluation
            {
                let quotient_eval_numer
                let y := mload(Y_MPTR)
                {
                    let f_13 := calldataload(0x0bc4)
                    let var0 := 0x2
                    let var1 := sub(R, f_13)
                    let var2 := addmod(var0, var1, R)
                    let var3 := mulmod(f_13, var2, R)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, R)
                    let var6 := mulmod(var3, var5, R)
                    let var7 := 0x4
                    let var8 := addmod(var7, var1, R)
                    let var9 := mulmod(var6, var8, R)
                    let a_4 := calldataload(0x0964)
                    let a_0 := calldataload(0x08e4)
                    let a_2 := calldataload(0x0924)
                    let var10 := addmod(a_0, a_2, R)
                    let var11 := sub(R, var10)
                    let var12 := addmod(a_4, var11, R)
                    let var13 := mulmod(var9, var12, R)
                    quotient_eval_numer := var13
                }
                {
                    let f_14 := calldataload(0x0be4)
                    let var0 := 0x2
                    let var1 := sub(R, f_14)
                    let var2 := addmod(var0, var1, R)
                    let var3 := mulmod(f_14, var2, R)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, R)
                    let var6 := mulmod(var3, var5, R)
                    let var7 := 0x4
                    let var8 := addmod(var7, var1, R)
                    let var9 := mulmod(var6, var8, R)
                    let a_5 := calldataload(0x0984)
                    let a_1 := calldataload(0x0904)
                    let a_3 := calldataload(0x0944)
                    let var10 := addmod(a_1, a_3, R)
                    let var11 := sub(R, var10)
                    let var12 := addmod(a_5, var11, R)
                    let var13 := mulmod(var9, var12, R)
                    quotient_eval_numer := addmod(
                        mulmod(quotient_eval_numer, y, r),
                        var13,
                        r
                    )
                }
                {
                    let f_13 := calldataload(0x0bc4)
                    let var0 := 0x1
                    let var1 := sub(R, f_13)
                    let var2 := addmod(var0, var1, R)
                    let var3 := mulmod(f_13, var2, R)
                    let var4 := 0x2
                    let var5 := addmod(var4, var1, R)
                    let var6 := mulmod(var3, var5, R)
                    let var7 := 0x4
                    let var8 := addmod(var7, var1, R)
                    let var9 := mulmod(var6, var8, R)
                    let a_4 := calldataload(0x0964)
                    let a_0 := calldataload(0x08e4)
                    let a_2 := calldataload(0x0924)
                    let var10 := mulmod(a_0, a_2, R)
                    let var11 := sub(R, var10)
                    let var12 := addmod(a_4, var11, R)
                    let var13 := mulmod(var9, var12, R)
                    quotient_eval_numer := addmod(
                        mulmod(quotient_eval_numer, y, r),
                        var13,
                        r
                    )
                }
                {
                    let f_14 := calldataload(0x0be4)
                    let var0 := 0x1
                    let var1 := sub(R, f_14)
                    let var2 := addmod(var0, var1, R)
                    let var3 := mulmod(f_14, var2, R)
                    let var4 := 0x2
                    let var5 := addmod(var4, var1, R)
                    let var6 := mulmod(var3, var5, R)
                    let var7 := 0x4
                    let var8 := addmod(var7, var1, R)
                    let var9 := mulmod(var6, var8, R)
                    let a_5 := calldataload(0x0984)
                    let a_1 := calldataload(0x0904)
                    let a_3 := calldataload(0x0944)
                    let var10 := mulmod(a_1, a_3, R)
                    let var11 := sub(R, var10)
                    let var12 := addmod(a_5, var11, R)
                    let var13 := mulmod(var9, var12, R)
                    quotient_eval_numer := addmod(
                        mulmod(quotient_eval_numer, y, r),
                        var13,
                        r
                    )
                }
                {
                    let f_13 := calldataload(0x0bc4)
                    let var0 := 0x1
                    let var1 := sub(R, f_13)
                    let var2 := addmod(var0, var1, R)
                    let var3 := mulmod(f_13, var2, R)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, R)
                    let var6 := mulmod(var3, var5, R)
                    let var7 := 0x4
                    let var8 := addmod(var7, var1, R)
                    let var9 := mulmod(var6, var8, R)
                    let a_4 := calldataload(0x0964)
                    let a_0 := calldataload(0x08e4)
                    let a_2 := calldataload(0x0924)
                    let var10 := sub(R, a_2)
                    let var11 := addmod(a_0, var10, R)
                    let var12 := sub(R, var11)
                    let var13 := addmod(a_4, var12, R)
                    let var14 := mulmod(var9, var13, R)
                    quotient_eval_numer := addmod(
                        mulmod(quotient_eval_numer, y, r),
                        var14,
                        r
                    )
                }
                {
                    let f_14 := calldataload(0x0be4)
                    let var0 := 0x1
                    let var1 := sub(R, f_14)
                    let var2 := addmod(var0, var1, R)
                    let var3 := mulmod(f_14, var2, R)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, R)
                    let var6 := mulmod(var3, var5, R)
                    let var7 := 0x4
                    let var8 := addmod(var7, var1, R)
                    let var9 := mulmod(var6, var8, R)
                    let a_5 := calldataload(0x0984)
                    let a_1 := calldataload(0x0904)
                    let a_3 := calldataload(0x0944)
                    let var10 := sub(R, a_3)
                    let var11 := addmod(a_1, var10, R)
                    let var12 := sub(R, var11)
                    let var13 := addmod(a_5, var12, R)
                    let var14 := mulmod(var9, var13, R)
                    quotient_eval_numer := addmod(
                        mulmod(quotient_eval_numer, y, r),
                        var14,
                        r
                    )
                }
                {
                    let f_13 := calldataload(0x0bc4)
                    let var0 := 0x1
                    let var1 := sub(R, f_13)
                    let var2 := addmod(var0, var1, R)
                    let var3 := mulmod(f_13, var2, R)
                    let var4 := 0x2
                    let var5 := addmod(var4, var1, R)
                    let var6 := mulmod(var3, var5, R)
                    let var7 := 0x3
                    let var8 := addmod(var7, var1, R)
                    let var9 := mulmod(var6, var8, R)
                    let a_4 := calldataload(0x0964)
                    let var10 := sub(R, var0)
                    let var11 := addmod(a_4, var10, R)
                    let var12 := mulmod(a_4, var11, R)
                    let var13 := mulmod(var9, var12, R)
                    quotient_eval_numer := addmod(
                        mulmod(quotient_eval_numer, y, r),
                        var13,
                        r
                    )
                }
                {
                    let f_14 := calldataload(0x0be4)
                    let var0 := 0x1
                    let var1 := sub(R, f_14)
                    let var2 := addmod(var0, var1, R)
                    let var3 := mulmod(f_14, var2, R)
                    let var4 := 0x2
                    let var5 := addmod(var4, var1, R)
                    let var6 := mulmod(var3, var5, R)
                    let var7 := 0x3
                    let var8 := addmod(var7, var1, R)
                    let var9 := mulmod(var6, var8, R)
                    let a_5 := calldataload(0x0984)
                    let var10 := sub(R, var0)
                    let var11 := addmod(a_5, var10, R)
                    let var12 := mulmod(a_5, var11, R)
                    let var13 := mulmod(var9, var12, R)
                    quotient_eval_numer := addmod(
                        mulmod(quotient_eval_numer, y, r),
                        var13,
                        r
                    )
                }
                {
                    let f_15 := calldataload(0x0c04)
                    let var0 := 0x1
                    let var1 := sub(R, f_15)
                    let var2 := addmod(var0, var1, R)
                    let var3 := mulmod(f_15, var2, R)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, R)
                    let var6 := mulmod(var3, var5, R)
                    let a_4 := calldataload(0x0964)
                    let a_4_prev_1 := calldataload(0x0a04)
                    let var7 := 0x0
                    let a_0 := calldataload(0x08e4)
                    let a_2 := calldataload(0x0924)
                    let var8 := mulmod(a_0, a_2, R)
                    let var9 := addmod(var7, var8, R)
                    let a_1 := calldataload(0x0904)
                    let a_3 := calldataload(0x0944)
                    let var10 := mulmod(a_1, a_3, R)
                    let var11 := addmod(var9, var10, R)
                    let var12 := addmod(a_4_prev_1, var11, R)
                    let var13 := sub(R, var12)
                    let var14 := addmod(a_4, var13, R)
                    let var15 := mulmod(var6, var14, R)
                    quotient_eval_numer := addmod(
                        mulmod(quotient_eval_numer, y, r),
                        var15,
                        r
                    )
                }
                {
                    let f_15 := calldataload(0x0c04)
                    let var0 := 0x2
                    let var1 := sub(R, f_15)
                    let var2 := addmod(var0, var1, R)
                    let var3 := mulmod(f_15, var2, R)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, R)
                    let var6 := mulmod(var3, var5, R)
                    let a_4 := calldataload(0x0964)
                    let var7 := 0x0
                    let a_0 := calldataload(0x08e4)
                    let a_2 := calldataload(0x0924)
                    let var8 := mulmod(a_0, a_2, R)
                    let var9 := addmod(var7, var8, R)
                    let a_1 := calldataload(0x0904)
                    let a_3 := calldataload(0x0944)
                    let var10 := mulmod(a_1, a_3, R)
                    let var11 := addmod(var9, var10, R)
                    let var12 := sub(R, var11)
                    let var13 := addmod(a_4, var12, R)
                    let var14 := mulmod(var6, var13, R)
                    quotient_eval_numer := addmod(
                        mulmod(quotient_eval_numer, y, r),
                        var14,
                        r
                    )
                }
                {
                    let f_16 := calldataload(0x0c24)
                    let var0 := 0x2
                    let var1 := sub(R, f_16)
                    let var2 := addmod(var0, var1, R)
                    let var3 := mulmod(f_16, var2, R)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, R)
                    let var6 := mulmod(var3, var5, R)
                    let a_4 := calldataload(0x0964)
                    let var7 := 0x1
                    let a_2 := calldataload(0x0924)
                    let var8 := mulmod(var7, a_2, R)
                    let a_3 := calldataload(0x0944)
                    let var9 := mulmod(var8, a_3, R)
                    let var10 := sub(R, var9)
                    let var11 := addmod(a_4, var10, R)
                    let var12 := mulmod(var6, var11, R)
                    quotient_eval_numer := addmod(
                        mulmod(quotient_eval_numer, y, r),
                        var12,
                        r
                    )
                }
                {
                    let f_15 := calldataload(0x0c04)
                    let var0 := 0x1
                    let var1 := sub(R, f_15)
                    let var2 := addmod(var0, var1, R)
                    let var3 := mulmod(f_15, var2, R)
                    let var4 := 0x2
                    let var5 := addmod(var4, var1, R)
                    let var6 := mulmod(var3, var5, R)
                    let a_4 := calldataload(0x0964)
                    let a_4_prev_1 := calldataload(0x0a04)
                    let a_2 := calldataload(0x0924)
                    let var7 := mulmod(var0, a_2, R)
                    let a_3 := calldataload(0x0944)
                    let var8 := mulmod(var7, a_3, R)
                    let var9 := mulmod(a_4_prev_1, var8, R)
                    let var10 := sub(R, var9)
                    let var11 := addmod(a_4, var10, R)
                    let var12 := mulmod(var6, var11, R)
                    quotient_eval_numer := addmod(
                        mulmod(quotient_eval_numer, y, r),
                        var12,
                        r
                    )
                }
                {
                    let f_16 := calldataload(0x0c24)
                    let var0 := 0x1
                    let var1 := sub(R, f_16)
                    let var2 := addmod(var0, var1, R)
                    let var3 := mulmod(f_16, var2, R)
                    let var4 := 0x2
                    let var5 := addmod(var4, var1, R)
                    let var6 := mulmod(var3, var5, R)
                    let a_4 := calldataload(0x0964)
                    let var7 := 0x0
                    let a_2 := calldataload(0x0924)
                    let var8 := addmod(var7, a_2, R)
                    let a_3 := calldataload(0x0944)
                    let var9 := addmod(var8, a_3, R)
                    let var10 := sub(R, var9)
                    let var11 := addmod(a_4, var10, R)
                    let var12 := mulmod(var6, var11, R)
                    quotient_eval_numer := addmod(
                        mulmod(quotient_eval_numer, y, r),
                        var12,
                        r
                    )
                }
                {
                    let f_16 := calldataload(0x0c24)
                    let var0 := 0x1
                    let var1 := sub(R, f_16)
                    let var2 := addmod(var0, var1, R)
                    let var3 := mulmod(f_16, var2, R)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, R)
                    let var6 := mulmod(var3, var5, R)
                    let a_4 := calldataload(0x0964)
                    let a_4_prev_1 := calldataload(0x0a04)
                    let var7 := 0x0
                    let a_2 := calldataload(0x0924)
                    let var8 := addmod(var7, a_2, R)
                    let a_3 := calldataload(0x0944)
                    let var9 := addmod(var8, a_3, R)
                    let var10 := addmod(a_4_prev_1, var9, R)
                    let var11 := sub(R, var10)
                    let var12 := addmod(a_4, var11, R)
                    let var13 := mulmod(var6, var12, R)
                    quotient_eval_numer := addmod(
                        mulmod(quotient_eval_numer, y, r),
                        var13,
                        r
                    )
                }
                {
                    let l_0 := mload(L_0_MPTR)
                    let eval := addmod(
                        l_0,
                        sub(R, mulmod(l_0, calldataload(0x0dc4), R)),
                        R
                    )
                    quotient_eval_numer := addmod(
                        mulmod(quotient_eval_numer, y, r),
                        eval,
                        r
                    )
                }
                {
                    let perm_z_last := calldataload(0x0e84)
                    let eval := mulmod(
                        mload(L_LAST_MPTR),
                        addmod(
                            mulmod(perm_z_last, perm_z_last, R),
                            sub(R, perm_z_last),
                            R
                        ),
                        R
                    )
                    quotient_eval_numer := addmod(
                        mulmod(quotient_eval_numer, y, r),
                        eval,
                        r
                    )
                }
                {
                    let eval := mulmod(
                        mload(L_0_MPTR),
                        addmod(
                            calldataload(0x0e24),
                            sub(R, calldataload(0x0e04)),
                            R
                        ),
                        R
                    )
                    quotient_eval_numer := addmod(
                        mulmod(quotient_eval_numer, y, r),
                        eval,
                        r
                    )
                }
                {
                    let eval := mulmod(
                        mload(L_0_MPTR),
                        addmod(
                            calldataload(0x0e84),
                            sub(R, calldataload(0x0e64)),
                            R
                        ),
                        R
                    )
                    quotient_eval_numer := addmod(
                        mulmod(quotient_eval_numer, y, r),
                        eval,
                        r
                    )
                }
                {
                    let gamma := mload(GAMMA_MPTR)
                    let beta := mload(BETA_MPTR)
                    let lhs := calldataload(0x0de4)
                    let rhs := calldataload(0x0dc4)
                    lhs := mulmod(
                        lhs,
                        addmod(
                            addmod(
                                calldataload(0x08e4),
                                mulmod(beta, calldataload(0x0c64), R),
                                R
                            ),
                            gamma,
                            R
                        ),
                        R
                    )
                    lhs := mulmod(
                        lhs,
                        addmod(
                            addmod(
                                calldataload(0x0904),
                                mulmod(beta, calldataload(0x0c84), R),
                                R
                            ),
                            gamma,
                            R
                        ),
                        R
                    )
                    lhs := mulmod(
                        lhs,
                        addmod(
                            addmod(
                                calldataload(0x0924),
                                mulmod(beta, calldataload(0x0ca4), R),
                                R
                            ),
                            gamma,
                            R
                        ),
                        R
                    )
                    lhs := mulmod(
                        lhs,
                        addmod(
                            addmod(
                                calldataload(0x0944),
                                mulmod(beta, calldataload(0x0cc4), R),
                                R
                            ),
                            gamma,
                            R
                        ),
                        R
                    )
                    mstore(0x00, mulmod(beta, mload(X_MPTR), R))
                    rhs := mulmod(
                        rhs,
                        addmod(
                            addmod(calldataload(0x08e4), mload(0x00), R),
                            gamma,
                            R
                        ),
                        R
                    )
                    mstore(0x00, mulmod(mload(0x00), DELTA, R))
                    rhs := mulmod(
                        rhs,
                        addmod(
                            addmod(calldataload(0x0904), mload(0x00), R),
                            gamma,
                            R
                        ),
                        R
                    )
                    mstore(0x00, mulmod(mload(0x00), DELTA, R))
                    rhs := mulmod(
                        rhs,
                        addmod(
                            addmod(calldataload(0x0924), mload(0x00), R),
                            gamma,
                            R
                        ),
                        R
                    )
                    mstore(0x00, mulmod(mload(0x00), DELTA, R))
                    rhs := mulmod(
                        rhs,
                        addmod(
                            addmod(calldataload(0x0944), mload(0x00), R),
                            gamma,
                            R
                        ),
                        R
                    )
                    mstore(0x00, mulmod(mload(0x00), DELTA, R))
                    let left_sub_right := addmod(lhs, sub(R, rhs), R)
                    let eval := addmod(
                        left_sub_right,
                        sub(
                            R,
                            mulmod(
                                left_sub_right,
                                addmod(
                                    mload(L_LAST_MPTR),
                                    mload(L_BLIND_MPTR),
                                    R
                                ),
                                R
                            )
                        ),
                        R
                    )
                    quotient_eval_numer := addmod(
                        mulmod(quotient_eval_numer, y, r),
                        eval,
                        r
                    )
                }
                {
                    let gamma := mload(GAMMA_MPTR)
                    let beta := mload(BETA_MPTR)
                    let lhs := calldataload(0x0e44)
                    let rhs := calldataload(0x0e24)
                    lhs := mulmod(
                        lhs,
                        addmod(
                            addmod(
                                calldataload(0x0964),
                                mulmod(beta, calldataload(0x0ce4), R),
                                R
                            ),
                            gamma,
                            R
                        ),
                        R
                    )
                    lhs := mulmod(
                        lhs,
                        addmod(
                            addmod(
                                calldataload(0x0984),
                                mulmod(beta, calldataload(0x0d04), R),
                                R
                            ),
                            gamma,
                            R
                        ),
                        R
                    )
                    lhs := mulmod(
                        lhs,
                        addmod(
                            addmod(
                                calldataload(0x09a4),
                                mulmod(beta, calldataload(0x0d24), R),
                                R
                            ),
                            gamma,
                            R
                        ),
                        R
                    )
                    lhs := mulmod(
                        lhs,
                        addmod(
                            addmod(
                                calldataload(0x09c4),
                                mulmod(beta, calldataload(0x0d44), R),
                                R
                            ),
                            gamma,
                            R
                        ),
                        R
                    )
                    rhs := mulmod(
                        rhs,
                        addmod(
                            addmod(calldataload(0x0964), mload(0x00), R),
                            gamma,
                            R
                        ),
                        R
                    )
                    mstore(0x00, mulmod(mload(0x00), DELTA, R))
                    rhs := mulmod(
                        rhs,
                        addmod(
                            addmod(calldataload(0x0984), mload(0x00), R),
                            gamma,
                            R
                        ),
                        R
                    )
                    mstore(0x00, mulmod(mload(0x00), DELTA, R))
                    rhs := mulmod(
                        rhs,
                        addmod(
                            addmod(calldataload(0x09a4), mload(0x00), R),
                            gamma,
                            R
                        ),
                        R
                    )
                    mstore(0x00, mulmod(mload(0x00), DELTA, R))
                    rhs := mulmod(
                        rhs,
                        addmod(
                            addmod(calldataload(0x09c4), mload(0x00), R),
                            gamma,
                            R
                        ),
                        R
                    )
                    mstore(0x00, mulmod(mload(0x00), DELTA, R))
                    let left_sub_right := addmod(lhs, sub(R, rhs), R)
                    let eval := addmod(
                        left_sub_right,
                        sub(
                            R,
                            mulmod(
                                left_sub_right,
                                addmod(
                                    mload(L_LAST_MPTR),
                                    mload(L_BLIND_MPTR),
                                    R
                                ),
                                R
                            )
                        ),
                        R
                    )
                    quotient_eval_numer := addmod(
                        mulmod(quotient_eval_numer, y, r),
                        eval,
                        r
                    )
                }
                {
                    let gamma := mload(GAMMA_MPTR)
                    let beta := mload(BETA_MPTR)
                    let lhs := calldataload(0x0ea4)
                    let rhs := calldataload(0x0e84)
                    lhs := mulmod(
                        lhs,
                        addmod(
                            addmod(
                                calldataload(0x09e4),
                                mulmod(beta, calldataload(0x0d64), R),
                                R
                            ),
                            gamma,
                            R
                        ),
                        R
                    )
                    lhs := mulmod(
                        lhs,
                        addmod(
                            addmod(
                                calldataload(0x0a24),
                                mulmod(beta, calldataload(0x0d84), R),
                                R
                            ),
                            gamma,
                            R
                        ),
                        R
                    )
                    lhs := mulmod(
                        lhs,
                        addmod(
                            addmod(
                                mload(INSTANCE_EVAL_MPTR),
                                mulmod(beta, calldataload(0x0da4), R),
                                R
                            ),
                            gamma,
                            R
                        ),
                        R
                    )
                    rhs := mulmod(
                        rhs,
                        addmod(
                            addmod(calldataload(0x09e4), mload(0x00), R),
                            gamma,
                            R
                        ),
                        R
                    )
                    mstore(0x00, mulmod(mload(0x00), DELTA, R))
                    rhs := mulmod(
                        rhs,
                        addmod(
                            addmod(calldataload(0x0a24), mload(0x00), R),
                            gamma,
                            R
                        ),
                        R
                    )
                    mstore(0x00, mulmod(mload(0x00), DELTA, R))
                    rhs := mulmod(
                        rhs,
                        addmod(
                            addmod(mload(INSTANCE_EVAL_MPTR), mload(0x00), R),
                            gamma,
                            R
                        ),
                        R
                    )
                    let left_sub_right := addmod(lhs, sub(R, rhs), R)
                    let eval := addmod(
                        left_sub_right,
                        sub(
                            R,
                            mulmod(
                                left_sub_right,
                                addmod(
                                    mload(L_LAST_MPTR),
                                    mload(L_BLIND_MPTR),
                                    R
                                ),
                                R
                            )
                        ),
                        R
                    )
                    quotient_eval_numer := addmod(
                        mulmod(quotient_eval_numer, y, r),
                        eval,
                        r
                    )
                }
                {
                    let l_0 := mload(L_0_MPTR)
                    let eval := mulmod(l_0, calldataload(0x0ec4), R)
                    quotient_eval_numer := addmod(
                        mulmod(quotient_eval_numer, y, r),
                        eval,
                        r
                    )
                }
                {
                    let l_last := mload(L_LAST_MPTR)
                    let eval := mulmod(l_last, calldataload(0x0ec4), R)
                    quotient_eval_numer := addmod(
                        mulmod(quotient_eval_numer, y, r),
                        eval,
                        r
                    )
                }
                {
                    let theta := mload(THETA_MPTR)
                    let beta := mload(BETA_MPTR)
                    let table
                    {
                        let var0 := 0x1
                        let f_7 := calldataload(0x0b04)
                        let var1 := mulmod(var0, f_7, R)
                        let a_6 := calldataload(0x09a4)
                        let var2 := mulmod(a_6, f_7, R)
                        let a_7 := calldataload(0x09c4)
                        let var3 := mulmod(a_7, f_7, R)
                        let a_8 := calldataload(0x09e4)
                        let var4 := mulmod(a_8, f_7, R)
                        table := var1
                        table := addmod(mulmod(table, theta, R), var2, R)
                        table := addmod(mulmod(table, theta, R), var3, R)
                        table := addmod(mulmod(table, theta, R), var4, R)
                        table := addmod(table, beta, R)
                    }
                    let input_0
                    {
                        let var0 := 0x1
                        let f_8 := calldataload(0x0b24)
                        let var1 := mulmod(var0, f_8, R)
                        let a_0 := calldataload(0x08e4)
                        let var2 := mulmod(a_0, f_8, R)
                        let a_2 := calldataload(0x0924)
                        let var3 := mulmod(a_2, f_8, R)
                        let a_4 := calldataload(0x0964)
                        let var4 := mulmod(a_4, f_8, R)
                        input_0 := var1
                        input_0 := addmod(mulmod(input_0, theta, R), var2, R)
                        input_0 := addmod(mulmod(input_0, theta, R), var3, R)
                        input_0 := addmod(mulmod(input_0, theta, R), var4, R)
                        input_0 := addmod(input_0, beta, R)
                    }
                    let lhs
                    let rhs
                    rhs := table
                    {
                        let tmp := input_0
                        rhs := addmod(
                            rhs,
                            sub(R, mulmod(calldataload(0x0f04), tmp, R)),
                            R
                        )
                        lhs := mulmod(
                            mulmod(table, tmp, R),
                            addmod(
                                calldataload(0x0ee4),
                                sub(R, calldataload(0x0ec4)),
                                R
                            ),
                            R
                        )
                    }
                    let eval := mulmod(
                        addmod(
                            1,
                            sub(
                                R,
                                addmod(
                                    mload(L_BLIND_MPTR),
                                    mload(L_LAST_MPTR),
                                    R
                                )
                            ),
                            R
                        ),
                        addmod(lhs, sub(R, rhs), R),
                        R
                    )
                    quotient_eval_numer := addmod(
                        mulmod(quotient_eval_numer, y, r),
                        eval,
                        r
                    )
                }
                {
                    let l_0 := mload(L_0_MPTR)
                    let eval := mulmod(l_0, calldataload(0x0f24), R)
                    quotient_eval_numer := addmod(
                        mulmod(quotient_eval_numer, y, r),
                        eval,
                        r
                    )
                }
                {
                    let l_last := mload(L_LAST_MPTR)
                    let eval := mulmod(l_last, calldataload(0x0f24), R)
                    quotient_eval_numer := addmod(
                        mulmod(quotient_eval_numer, y, r),
                        eval,
                        r
                    )
                }
                {
                    let theta := mload(THETA_MPTR)
                    let beta := mload(BETA_MPTR)
                    let table
                    {
                        let var0 := 0x1
                        let f_7 := calldataload(0x0b04)
                        let var1 := mulmod(var0, f_7, R)
                        let a_6 := calldataload(0x09a4)
                        let var2 := mulmod(a_6, f_7, R)
                        let a_7 := calldataload(0x09c4)
                        let var3 := mulmod(a_7, f_7, R)
                        let a_8 := calldataload(0x09e4)
                        let var4 := mulmod(a_8, f_7, R)
                        table := var1
                        table := addmod(mulmod(table, theta, R), var2, R)
                        table := addmod(mulmod(table, theta, R), var3, R)
                        table := addmod(mulmod(table, theta, R), var4, R)
                        table := addmod(table, beta, R)
                    }
                    let input_0
                    {
                        let var0 := 0x1
                        let f_9 := calldataload(0x0b44)
                        let var1 := mulmod(var0, f_9, R)
                        let a_1 := calldataload(0x0904)
                        let var2 := mulmod(a_1, f_9, R)
                        let a_3 := calldataload(0x0944)
                        let var3 := mulmod(a_3, f_9, R)
                        let a_5 := calldataload(0x0984)
                        let var4 := mulmod(a_5, f_9, R)
                        input_0 := var1
                        input_0 := addmod(mulmod(input_0, theta, R), var2, R)
                        input_0 := addmod(mulmod(input_0, theta, R), var3, R)
                        input_0 := addmod(mulmod(input_0, theta, R), var4, R)
                        input_0 := addmod(input_0, beta, R)
                    }
                    let lhs
                    let rhs
                    rhs := table
                    {
                        let tmp := input_0
                        rhs := addmod(
                            rhs,
                            sub(R, mulmod(calldataload(0x0f64), tmp, R)),
                            R
                        )
                        lhs := mulmod(
                            mulmod(table, tmp, R),
                            addmod(
                                calldataload(0x0f44),
                                sub(R, calldataload(0x0f24)),
                                R
                            ),
                            R
                        )
                    }
                    let eval := mulmod(
                        addmod(
                            1,
                            sub(
                                R,
                                addmod(
                                    mload(L_BLIND_MPTR),
                                    mload(L_LAST_MPTR),
                                    R
                                )
                            ),
                            R
                        ),
                        addmod(lhs, sub(R, rhs), R),
                        R
                    )
                    quotient_eval_numer := addmod(
                        mulmod(quotient_eval_numer, y, r),
                        eval,
                        r
                    )
                }
                {
                    let l_0 := mload(L_0_MPTR)
                    let eval := mulmod(l_0, calldataload(0x0f84), R)
                    quotient_eval_numer := addmod(
                        mulmod(quotient_eval_numer, y, r),
                        eval,
                        r
                    )
                }
                {
                    let l_last := mload(L_LAST_MPTR)
                    let eval := mulmod(l_last, calldataload(0x0f84), R)
                    quotient_eval_numer := addmod(
                        mulmod(quotient_eval_numer, y, r),
                        eval,
                        r
                    )
                }
                {
                    let theta := mload(THETA_MPTR)
                    let beta := mload(BETA_MPTR)
                    let table
                    {
                        let var0 := 0x1
                        let f_10 := calldataload(0x0b64)
                        let var1 := mulmod(var0, f_10, R)
                        let a_6 := calldataload(0x09a4)
                        let var2 := mulmod(a_6, f_10, R)
                        let a_7 := calldataload(0x09c4)
                        let var3 := mulmod(a_7, f_10, R)
                        table := var1
                        table := addmod(mulmod(table, theta, R), var2, R)
                        table := addmod(mulmod(table, theta, R), var3, R)
                        table := addmod(table, beta, R)
                    }
                    let input_0
                    {
                        let var0 := 0x1
                        let f_11 := calldataload(0x0b84)
                        let var1 := mulmod(var0, f_11, R)
                        let a_0 := calldataload(0x08e4)
                        let var2 := mulmod(a_0, f_11, R)
                        let a_2 := calldataload(0x0924)
                        let var3 := mulmod(a_2, f_11, R)
                        input_0 := var1
                        input_0 := addmod(mulmod(input_0, theta, R), var2, R)
                        input_0 := addmod(mulmod(input_0, theta, R), var3, R)
                        input_0 := addmod(input_0, beta, R)
                    }
                    let lhs
                    let rhs
                    rhs := table
                    {
                        let tmp := input_0
                        rhs := addmod(
                            rhs,
                            sub(R, mulmod(calldataload(0x0fc4), tmp, R)),
                            R
                        )
                        lhs := mulmod(
                            mulmod(table, tmp, R),
                            addmod(
                                calldataload(0x0fa4),
                                sub(R, calldataload(0x0f84)),
                                R
                            ),
                            R
                        )
                    }
                    let eval := mulmod(
                        addmod(
                            1,
                            sub(
                                R,
                                addmod(
                                    mload(L_BLIND_MPTR),
                                    mload(L_LAST_MPTR),
                                    R
                                )
                            ),
                            R
                        ),
                        addmod(lhs, sub(R, rhs), R),
                        R
                    )
                    quotient_eval_numer := addmod(
                        mulmod(quotient_eval_numer, y, r),
                        eval,
                        r
                    )
                }
                {
                    let l_0 := mload(L_0_MPTR)
                    let eval := mulmod(l_0, calldataload(0x0fe4), R)
                    quotient_eval_numer := addmod(
                        mulmod(quotient_eval_numer, y, r),
                        eval,
                        r
                    )
                }
                {
                    let l_last := mload(L_LAST_MPTR)
                    let eval := mulmod(l_last, calldataload(0x0fe4), R)
                    quotient_eval_numer := addmod(
                        mulmod(quotient_eval_numer, y, r),
                        eval,
                        r
                    )
                }
                {
                    let theta := mload(THETA_MPTR)
                    let beta := mload(BETA_MPTR)
                    let table
                    {
                        let var0 := 0x1
                        let f_10 := calldataload(0x0b64)
                        let var1 := mulmod(var0, f_10, R)
                        let a_6 := calldataload(0x09a4)
                        let var2 := mulmod(a_6, f_10, R)
                        let a_7 := calldataload(0x09c4)
                        let var3 := mulmod(a_7, f_10, R)
                        table := var1
                        table := addmod(mulmod(table, theta, R), var2, R)
                        table := addmod(mulmod(table, theta, R), var3, R)
                        table := addmod(table, beta, R)
                    }
                    let input_0
                    {
                        let var0 := 0x1
                        let f_12 := calldataload(0x0ba4)
                        let var1 := mulmod(var0, f_12, R)
                        let a_1 := calldataload(0x0904)
                        let var2 := mulmod(a_1, f_12, R)
                        let a_3 := calldataload(0x0944)
                        let var3 := mulmod(a_3, f_12, R)
                        input_0 := var1
                        input_0 := addmod(mulmod(input_0, theta, R), var2, R)
                        input_0 := addmod(mulmod(input_0, theta, R), var3, R)
                        input_0 := addmod(input_0, beta, R)
                    }
                    let lhs
                    let rhs
                    rhs := table
                    {
                        let tmp := input_0
                        rhs := addmod(
                            rhs,
                            sub(R, mulmod(calldataload(0x1024), tmp, R)),
                            R
                        )
                        lhs := mulmod(
                            mulmod(table, tmp, R),
                            addmod(
                                calldataload(0x1004),
                                sub(R, calldataload(0x0fe4)),
                                R
                            ),
                            R
                        )
                    }
                    let eval := mulmod(
                        addmod(
                            1,
                            sub(
                                R,
                                addmod(
                                    mload(L_BLIND_MPTR),
                                    mload(L_LAST_MPTR),
                                    R
                                )
                            ),
                            R
                        ),
                        addmod(lhs, sub(R, rhs), R),
                        R
                    )
                    quotient_eval_numer := addmod(
                        mulmod(quotient_eval_numer, y, r),
                        eval,
                        r
                    )
                }
                {
                    let l_0 := mload(L_0_MPTR)
                    let eval := mulmod(l_0, calldataload(0x1044), R)
                    quotient_eval_numer := addmod(
                        mulmod(quotient_eval_numer, y, r),
                        eval,
                        r
                    )
                }
                {
                    let l_last := mload(L_LAST_MPTR)
                    let eval := mulmod(l_last, calldataload(0x1044), R)
                    quotient_eval_numer := addmod(
                        mulmod(quotient_eval_numer, y, r),
                        eval,
                        r
                    )
                }
                {
                    let theta := mload(THETA_MPTR)
                    let beta := mload(BETA_MPTR)
                    let table
                    {
                        let f_1 := calldataload(0x0a44)
                        table := f_1
                        table := addmod(table, beta, R)
                    }
                    let input_0
                    {
                        let f_3 := calldataload(0x0a84)
                        let var0 := 0x1
                        let var1 := mulmod(f_3, var0, R)
                        let a_0 := calldataload(0x08e4)
                        let var2 := mulmod(var1, a_0, R)
                        let var3 := sub(R, var1)
                        let var4 := addmod(var0, var3, R)
                        let
                            var5
                        := 0x30644e72e131a029b85045b68181585d2833e84879b9709143e1f593f0000000
                        let var6 := mulmod(var4, var5, R)
                        let var7 := addmod(var2, var6, R)
                        input_0 := var7
                        input_0 := addmod(input_0, beta, R)
                    }
                    let lhs
                    let rhs
                    rhs := table
                    {
                        let tmp := input_0
                        rhs := addmod(
                            rhs,
                            sub(R, mulmod(calldataload(0x1084), tmp, R)),
                            R
                        )
                        lhs := mulmod(
                            mulmod(table, tmp, R),
                            addmod(
                                calldataload(0x1064),
                                sub(R, calldataload(0x1044)),
                                R
                            ),
                            R
                        )
                    }
                    let eval := mulmod(
                        addmod(
                            1,
                            sub(
                                R,
                                addmod(
                                    mload(L_BLIND_MPTR),
                                    mload(L_LAST_MPTR),
                                    R
                                )
                            ),
                            R
                        ),
                        addmod(lhs, sub(R, rhs), R),
                        R
                    )
                    quotient_eval_numer := addmod(
                        mulmod(quotient_eval_numer, y, r),
                        eval,
                        r
                    )
                }
                {
                    let l_0 := mload(L_0_MPTR)
                    let eval := mulmod(l_0, calldataload(0x10a4), R)
                    quotient_eval_numer := addmod(
                        mulmod(quotient_eval_numer, y, r),
                        eval,
                        r
                    )
                }
                {
                    let l_last := mload(L_LAST_MPTR)
                    let eval := mulmod(l_last, calldataload(0x10a4), R)
                    quotient_eval_numer := addmod(
                        mulmod(quotient_eval_numer, y, r),
                        eval,
                        r
                    )
                }
                {
                    let theta := mload(THETA_MPTR)
                    let beta := mload(BETA_MPTR)
                    let table
                    {
                        let f_1 := calldataload(0x0a44)
                        table := f_1
                        table := addmod(table, beta, R)
                    }
                    let input_0
                    {
                        let f_4 := calldataload(0x0aa4)
                        let var0 := 0x1
                        let var1 := mulmod(f_4, var0, R)
                        let a_1 := calldataload(0x0904)
                        let var2 := mulmod(var1, a_1, R)
                        let var3 := sub(R, var1)
                        let var4 := addmod(var0, var3, R)
                        let
                            var5
                        := 0x30644e72e131a029b85045b68181585d2833e84879b9709143e1f593f0000000
                        let var6 := mulmod(var4, var5, R)
                        let var7 := addmod(var2, var6, R)
                        input_0 := var7
                        input_0 := addmod(input_0, beta, R)
                    }
                    let lhs
                    let rhs
                    rhs := table
                    {
                        let tmp := input_0
                        rhs := addmod(
                            rhs,
                            sub(R, mulmod(calldataload(0x10e4), tmp, R)),
                            R
                        )
                        lhs := mulmod(
                            mulmod(table, tmp, R),
                            addmod(
                                calldataload(0x10c4),
                                sub(R, calldataload(0x10a4)),
                                R
                            ),
                            R
                        )
                    }
                    let eval := mulmod(
                        addmod(
                            1,
                            sub(
                                R,
                                addmod(
                                    mload(L_BLIND_MPTR),
                                    mload(L_LAST_MPTR),
                                    R
                                )
                            ),
                            R
                        ),
                        addmod(lhs, sub(R, rhs), R),
                        R
                    )
                    quotient_eval_numer := addmod(
                        mulmod(quotient_eval_numer, y, r),
                        eval,
                        r
                    )
                }
                {
                    let l_0 := mload(L_0_MPTR)
                    let eval := mulmod(l_0, calldataload(0x1104), R)
                    quotient_eval_numer := addmod(
                        mulmod(quotient_eval_numer, y, r),
                        eval,
                        r
                    )
                }
                {
                    let l_last := mload(L_LAST_MPTR)
                    let eval := mulmod(l_last, calldataload(0x1104), R)
                    quotient_eval_numer := addmod(
                        mulmod(quotient_eval_numer, y, r),
                        eval,
                        r
                    )
                }
                {
                    let theta := mload(THETA_MPTR)
                    let beta := mload(BETA_MPTR)
                    let table
                    {
                        let f_2 := calldataload(0x0a64)
                        table := f_2
                        table := addmod(table, beta, R)
                    }
                    let input_0
                    {
                        let f_5 := calldataload(0x0ac4)
                        let var0 := 0x1
                        let var1 := mulmod(f_5, var0, R)
                        let a_0 := calldataload(0x08e4)
                        let var2 := mulmod(var1, a_0, R)
                        let var3 := sub(R, var1)
                        let var4 := addmod(var0, var3, R)
                        let var5 := 0x0
                        let var6 := mulmod(var4, var5, R)
                        let var7 := addmod(var2, var6, R)
                        input_0 := var7
                        input_0 := addmod(input_0, beta, R)
                    }
                    let lhs
                    let rhs
                    rhs := table
                    {
                        let tmp := input_0
                        rhs := addmod(
                            rhs,
                            sub(R, mulmod(calldataload(0x1144), tmp, R)),
                            R
                        )
                        lhs := mulmod(
                            mulmod(table, tmp, R),
                            addmod(
                                calldataload(0x1124),
                                sub(R, calldataload(0x1104)),
                                R
                            ),
                            R
                        )
                    }
                    let eval := mulmod(
                        addmod(
                            1,
                            sub(
                                R,
                                addmod(
                                    mload(L_BLIND_MPTR),
                                    mload(L_LAST_MPTR),
                                    R
                                )
                            ),
                            R
                        ),
                        addmod(lhs, sub(R, rhs), R),
                        R
                    )
                    quotient_eval_numer := addmod(
                        mulmod(quotient_eval_numer, y, r),
                        eval,
                        r
                    )
                }
                {
                    let l_0 := mload(L_0_MPTR)
                    let eval := mulmod(l_0, calldataload(0x1164), R)
                    quotient_eval_numer := addmod(
                        mulmod(quotient_eval_numer, y, r),
                        eval,
                        r
                    )
                }
                {
                    let l_last := mload(L_LAST_MPTR)
                    let eval := mulmod(l_last, calldataload(0x1164), R)
                    quotient_eval_numer := addmod(
                        mulmod(quotient_eval_numer, y, r),
                        eval,
                        r
                    )
                }
                {
                    let theta := mload(THETA_MPTR)
                    let beta := mload(BETA_MPTR)
                    let table
                    {
                        let f_2 := calldataload(0x0a64)
                        table := f_2
                        table := addmod(table, beta, R)
                    }
                    let input_0
                    {
                        let f_6 := calldataload(0x0ae4)
                        let var0 := 0x1
                        let var1 := mulmod(f_6, var0, R)
                        let a_1 := calldataload(0x0904)
                        let var2 := mulmod(var1, a_1, R)
                        let var3 := sub(R, var1)
                        let var4 := addmod(var0, var3, R)
                        let var5 := 0x0
                        let var6 := mulmod(var4, var5, R)
                        let var7 := addmod(var2, var6, R)
                        input_0 := var7
                        input_0 := addmod(input_0, beta, R)
                    }
                    let lhs
                    let rhs
                    rhs := table
                    {
                        let tmp := input_0
                        rhs := addmod(
                            rhs,
                            sub(R, mulmod(calldataload(0x11a4), tmp, R)),
                            R
                        )
                        lhs := mulmod(
                            mulmod(table, tmp, R),
                            addmod(
                                calldataload(0x1184),
                                sub(R, calldataload(0x1164)),
                                R
                            ),
                            R
                        )
                    }
                    let eval := mulmod(
                        addmod(
                            1,
                            sub(
                                R,
                                addmod(
                                    mload(L_BLIND_MPTR),
                                    mload(L_LAST_MPTR),
                                    R
                                )
                            ),
                            R
                        ),
                        addmod(lhs, sub(R, rhs), R),
                        R
                    )
                    quotient_eval_numer := addmod(
                        mulmod(quotient_eval_numer, y, r),
                        eval,
                        r
                    )
                }

                pop(y)

                let quotient_eval := mulmod(
                    quotient_eval_numer,
                    mload(X_N_MINUS_1_INV_MPTR),
                    r
                )
                mstore(QUOTIENT_EVAL_MPTR, quotient_eval)
            }

            // Compute quotient commitment
            {
                mstore(0x00, calldataload(LAST_QUOTIENT_X_CPTR))
                mstore(0x20, calldataload(add(LAST_QUOTIENT_X_CPTR, 0x20)))
                let x_n := mload(X_N_MPTR)
                for {
                    let cptr := sub(LAST_QUOTIENT_X_CPTR, 0x40)
                    let cptr_end := sub(FIRST_QUOTIENT_X_CPTR, 0x40)
                } lt(cptr_end, cptr) {

                } {
                    success := ec_mul_acc(success, x_n)
                    success := ec_add_acc(
                        success,
                        calldataload(cptr),
                        calldataload(add(cptr, 0x20))
                    )
                    cptr := sub(cptr, 0x40)
                }
                mstore(QUOTIENT_X_MPTR, mload(0x00))
                mstore(QUOTIENT_Y_MPTR, mload(0x20))
            }

            // Compute pairing lhs and rhs
            {
                {
                    let x := mload(X_MPTR)
                    let omega := mload(OMEGA_MPTR)
                    let omega_inv := mload(OMEGA_INV_MPTR)
                    let x_pow_of_omega := mulmod(x, omega, R)
                    mstore(0x0360, x_pow_of_omega)
                    mstore(0x0340, x)
                    x_pow_of_omega := mulmod(x, omega_inv, R)
                    mstore(0x0320, x_pow_of_omega)
                    x_pow_of_omega := mulmod(x_pow_of_omega, omega_inv, R)
                    x_pow_of_omega := mulmod(x_pow_of_omega, omega_inv, R)
                    x_pow_of_omega := mulmod(x_pow_of_omega, omega_inv, R)
                    x_pow_of_omega := mulmod(x_pow_of_omega, omega_inv, R)
                    x_pow_of_omega := mulmod(x_pow_of_omega, omega_inv, R)
                    mstore(0x0300, x_pow_of_omega)
                }
                {
                    let mu := mload(MU_MPTR)
                    for {
                        let mptr := 0x0380
                        let mptr_end := 0x0400
                        let point_mptr := 0x0300
                    } lt(mptr, mptr_end) {
                        mptr := add(mptr, 0x20)
                        point_mptr := add(point_mptr, 0x20)
                    } {
                        mstore(mptr, addmod(mu, sub(R, mload(point_mptr)), R))
                    }
                    let s
                    s := mload(0x03c0)
                    mstore(0x0400, s)
                    let diff
                    diff := mload(0x0380)
                    diff := mulmod(diff, mload(0x03a0), R)
                    diff := mulmod(diff, mload(0x03e0), R)
                    mstore(0x0420, diff)
                    mstore(0x00, diff)
                    diff := mload(0x0380)
                    diff := mulmod(diff, mload(0x03e0), R)
                    mstore(0x0440, diff)
                    diff := mload(0x03a0)
                    mstore(0x0460, diff)
                    diff := mload(0x0380)
                    diff := mulmod(diff, mload(0x03a0), R)
                    mstore(0x0480, diff)
                }
                {
                    let point_2 := mload(0x0340)
                    let coeff
                    coeff := 1
                    coeff := mulmod(coeff, mload(0x03c0), R)
                    mstore(0x20, coeff)
                }
                {
                    let point_1 := mload(0x0320)
                    let point_2 := mload(0x0340)
                    let coeff
                    coeff := addmod(point_1, sub(R, point_2), R)
                    coeff := mulmod(coeff, mload(0x03a0), R)
                    mstore(0x40, coeff)
                    coeff := addmod(point_2, sub(R, point_1), R)
                    coeff := mulmod(coeff, mload(0x03c0), R)
                    mstore(0x60, coeff)
                }
                {
                    let point_0 := mload(0x0300)
                    let point_2 := mload(0x0340)
                    let point_3 := mload(0x0360)
                    let coeff
                    coeff := addmod(point_0, sub(R, point_2), R)
                    coeff := mulmod(
                        coeff,
                        addmod(point_0, sub(R, point_3), R),
                        R
                    )
                    coeff := mulmod(coeff, mload(0x0380), R)
                    mstore(0x80, coeff)
                    coeff := addmod(point_2, sub(R, point_0), R)
                    coeff := mulmod(
                        coeff,
                        addmod(point_2, sub(R, point_3), R),
                        R
                    )
                    coeff := mulmod(coeff, mload(0x03c0), R)
                    mstore(0xa0, coeff)
                    coeff := addmod(point_3, sub(R, point_0), R)
                    coeff := mulmod(
                        coeff,
                        addmod(point_3, sub(R, point_2), R),
                        R
                    )
                    coeff := mulmod(coeff, mload(0x03e0), R)
                    mstore(0xc0, coeff)
                }
                {
                    let point_2 := mload(0x0340)
                    let point_3 := mload(0x0360)
                    let coeff
                    coeff := addmod(point_2, sub(R, point_3), R)
                    coeff := mulmod(coeff, mload(0x03c0), R)
                    mstore(0xe0, coeff)
                    coeff := addmod(point_3, sub(R, point_2), R)
                    coeff := mulmod(coeff, mload(0x03e0), R)
                    mstore(0x0100, coeff)
                }
                {
                    success := batch_invert(success, 0, 0x0120)
                    let diff_0_inv := mload(0x00)
                    mstore(0x0420, diff_0_inv)
                    for {
                        let mptr := 0x0440
                        let mptr_end := 0x04a0
                    } lt(mptr, mptr_end) {
                        mptr := add(mptr, 0x20)
                    } {
                        mstore(mptr, mulmod(mload(mptr), diff_0_inv, R))
                    }
                }
                {
                    let coeff := mload(0x20)
                    let zeta := mload(ZETA_MPTR)
                    let r_eval := 0
                    r_eval := addmod(
                        r_eval,
                        mulmod(coeff, calldataload(0x0c44), R),
                        R
                    )
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(
                        r_eval,
                        mulmod(coeff, mload(QUOTIENT_EVAL_MPTR), R),
                        R
                    )
                    for {
                        let mptr := 0x0da4
                        let mptr_end := 0x0c44
                    } lt(mptr_end, mptr) {
                        mptr := sub(mptr, 0x20)
                    } {
                        r_eval := addmod(
                            mulmod(r_eval, zeta, R),
                            mulmod(coeff, calldataload(mptr), R),
                            R
                        )
                    }
                    for {
                        let mptr := 0x0c24
                        let mptr_end := 0x0a04
                    } lt(mptr_end, mptr) {
                        mptr := sub(mptr, 0x20)
                    } {
                        r_eval := addmod(
                            mulmod(r_eval, zeta, R),
                            mulmod(coeff, calldataload(mptr), R),
                            R
                        )
                    }
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(
                        r_eval,
                        mulmod(coeff, calldataload(0x11a4), R),
                        R
                    )
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(
                        r_eval,
                        mulmod(coeff, calldataload(0x1144), R),
                        R
                    )
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(
                        r_eval,
                        mulmod(coeff, calldataload(0x10e4), R),
                        R
                    )
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(
                        r_eval,
                        mulmod(coeff, calldataload(0x1084), R),
                        R
                    )
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(
                        r_eval,
                        mulmod(coeff, calldataload(0x1024), R),
                        R
                    )
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(
                        r_eval,
                        mulmod(coeff, calldataload(0x0fc4), R),
                        R
                    )
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(
                        r_eval,
                        mulmod(coeff, calldataload(0x0f64), R),
                        R
                    )
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(
                        r_eval,
                        mulmod(coeff, calldataload(0x0f04), R),
                        R
                    )
                    for {
                        let mptr := 0x09e4
                        let mptr_end := 0x0964
                    } lt(mptr_end, mptr) {
                        mptr := sub(mptr, 0x20)
                    } {
                        r_eval := addmod(
                            mulmod(r_eval, zeta, R),
                            mulmod(coeff, calldataload(mptr), R),
                            R
                        )
                    }
                    for {
                        let mptr := 0x0944
                        let mptr_end := 0x08c4
                    } lt(mptr_end, mptr) {
                        mptr := sub(mptr, 0x20)
                    } {
                        r_eval := addmod(
                            mulmod(r_eval, zeta, R),
                            mulmod(coeff, calldataload(mptr), R),
                            R
                        )
                    }
                    mstore(0x04a0, r_eval)
                }
                {
                    let zeta := mload(ZETA_MPTR)
                    let r_eval := 0
                    r_eval := addmod(
                        r_eval,
                        mulmod(mload(0x40), calldataload(0x0a04), R),
                        R
                    )
                    r_eval := addmod(
                        r_eval,
                        mulmod(mload(0x60), calldataload(0x0964), R),
                        R
                    )
                    r_eval := mulmod(r_eval, mload(0x0440), R)
                    mstore(0x04c0, r_eval)
                }
                {
                    let zeta := mload(ZETA_MPTR)
                    let r_eval := 0
                    r_eval := addmod(
                        r_eval,
                        mulmod(mload(0x80), calldataload(0x0e64), R),
                        R
                    )
                    r_eval := addmod(
                        r_eval,
                        mulmod(mload(0xa0), calldataload(0x0e24), R),
                        R
                    )
                    r_eval := addmod(
                        r_eval,
                        mulmod(mload(0xc0), calldataload(0x0e44), R),
                        R
                    )
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(
                        r_eval,
                        mulmod(mload(0x80), calldataload(0x0e04), R),
                        R
                    )
                    r_eval := addmod(
                        r_eval,
                        mulmod(mload(0xa0), calldataload(0x0dc4), R),
                        R
                    )
                    r_eval := addmod(
                        r_eval,
                        mulmod(mload(0xc0), calldataload(0x0de4), R),
                        R
                    )
                    r_eval := mulmod(r_eval, mload(0x0460), R)
                    mstore(0x04e0, r_eval)
                }
                {
                    let zeta := mload(ZETA_MPTR)
                    let r_eval := 0
                    r_eval := addmod(
                        r_eval,
                        mulmod(mload(0xe0), calldataload(0x1164), R),
                        R
                    )
                    r_eval := addmod(
                        r_eval,
                        mulmod(mload(0x0100), calldataload(0x1184), R),
                        R
                    )
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(
                        r_eval,
                        mulmod(mload(0xe0), calldataload(0x1104), R),
                        R
                    )
                    r_eval := addmod(
                        r_eval,
                        mulmod(mload(0x0100), calldataload(0x1124), R),
                        R
                    )
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(
                        r_eval,
                        mulmod(mload(0xe0), calldataload(0x10a4), R),
                        R
                    )
                    r_eval := addmod(
                        r_eval,
                        mulmod(mload(0x0100), calldataload(0x10c4), R),
                        R
                    )
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(
                        r_eval,
                        mulmod(mload(0xe0), calldataload(0x1044), R),
                        R
                    )
                    r_eval := addmod(
                        r_eval,
                        mulmod(mload(0x0100), calldataload(0x1064), R),
                        R
                    )
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(
                        r_eval,
                        mulmod(mload(0xe0), calldataload(0x0fe4), R),
                        R
                    )
                    r_eval := addmod(
                        r_eval,
                        mulmod(mload(0x0100), calldataload(0x1004), R),
                        R
                    )
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(
                        r_eval,
                        mulmod(mload(0xe0), calldataload(0x0f84), R),
                        R
                    )
                    r_eval := addmod(
                        r_eval,
                        mulmod(mload(0x0100), calldataload(0x0fa4), R),
                        R
                    )
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(
                        r_eval,
                        mulmod(mload(0xe0), calldataload(0x0f24), R),
                        R
                    )
                    r_eval := addmod(
                        r_eval,
                        mulmod(mload(0x0100), calldataload(0x0f44), R),
                        R
                    )
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(
                        r_eval,
                        mulmod(mload(0xe0), calldataload(0x0ec4), R),
                        R
                    )
                    r_eval := addmod(
                        r_eval,
                        mulmod(mload(0x0100), calldataload(0x0ee4), R),
                        R
                    )
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(
                        r_eval,
                        mulmod(mload(0xe0), calldataload(0x0e84), R),
                        R
                    )
                    r_eval := addmod(
                        r_eval,
                        mulmod(mload(0x0100), calldataload(0x0ea4), R),
                        R
                    )
                    r_eval := mulmod(r_eval, mload(0x0480), R)
                    mstore(0x0500, r_eval)
                }
                {
                    let sum := mload(0x20)
                    mstore(0x0520, sum)
                }
                {
                    let sum := mload(0x40)
                    sum := addmod(sum, mload(0x60), R)
                    mstore(0x0540, sum)
                }
                {
                    let sum := mload(0x80)
                    sum := addmod(sum, mload(0xa0), R)
                    sum := addmod(sum, mload(0xc0), R)
                    mstore(0x0560, sum)
                }
                {
                    let sum := mload(0xe0)
                    sum := addmod(sum, mload(0x0100), R)
                    mstore(0x0580, sum)
                }
                {
                    for {
                        let mptr := 0x00
                        let mptr_end := 0x80
                        let sum_mptr := 0x0520
                    } lt(mptr, mptr_end) {
                        mptr := add(mptr, 0x20)
                        sum_mptr := add(sum_mptr, 0x20)
                    } {
                        mstore(mptr, mload(sum_mptr))
                    }
                    success := batch_invert(success, 0, 0x80)
                    let r_eval := mulmod(mload(0x60), mload(0x0500), R)
                    for {
                        let sum_inv_mptr := 0x40
                        let sum_inv_mptr_end := 0x80
                        let r_eval_mptr := 0x04e0
                    } lt(sum_inv_mptr, sum_inv_mptr_end) {
                        sum_inv_mptr := sub(sum_inv_mptr, 0x20)
                        r_eval_mptr := sub(r_eval_mptr, 0x20)
                    } {
                        r_eval := mulmod(r_eval, mload(NU_MPTR), R)
                        r_eval := addmod(
                            r_eval,
                            mulmod(mload(sum_inv_mptr), mload(r_eval_mptr), R),
                            R
                        )
                    }
                    mstore(R_EVAL_MPTR, r_eval)
                }
                {
                    let nu := mload(NU_MPTR)
                    mstore(0x00, calldataload(0x0764))
                    mstore(0x20, calldataload(0x0784))
                    success := ec_mul_acc(success, mload(ZETA_MPTR))
                    success := ec_add_acc(
                        success,
                        mload(QUOTIENT_X_MPTR),
                        mload(QUOTIENT_Y_MPTR)
                    )
                    for {
                        let mptr := 0x0f00
                        let mptr_end := 0x0800
                    } lt(mptr_end, mptr) {
                        mptr := sub(mptr, 0x40)
                    } {
                        success := ec_mul_acc(success, mload(ZETA_MPTR))
                        success := ec_add_acc(
                            success,
                            mload(mptr),
                            mload(add(mptr, 0x20))
                        )
                    }
                    for {
                        let mptr := 0x0464
                        let mptr_end := 0x0164
                    } lt(mptr_end, mptr) {
                        mptr := sub(mptr, 0x40)
                    } {
                        success := ec_mul_acc(success, mload(ZETA_MPTR))
                        success := ec_add_acc(
                            success,
                            calldataload(mptr),
                            calldataload(add(mptr, 0x20))
                        )
                    }
                    for {
                        let mptr := 0x0124
                        let mptr_end := 0x24
                    } lt(mptr_end, mptr) {
                        mptr := sub(mptr, 0x40)
                    } {
                        success := ec_mul_acc(success, mload(ZETA_MPTR))
                        success := ec_add_acc(
                            success,
                            calldataload(mptr),
                            calldataload(add(mptr, 0x20))
                        )
                    }
                    mstore(0x80, calldataload(0x0164))
                    mstore(0xa0, calldataload(0x0184))
                    success := ec_mul_tmp(success, mulmod(nu, mload(0x0440), R))
                    success := ec_add_acc(success, mload(0x80), mload(0xa0))
                    nu := mulmod(nu, mload(NU_MPTR), R)
                    mstore(0x80, calldataload(0x04e4))
                    mstore(0xa0, calldataload(0x0504))
                    success := ec_mul_tmp(success, mload(ZETA_MPTR))
                    success := ec_add_tmp(
                        success,
                        calldataload(0x04a4),
                        calldataload(0x04c4)
                    )
                    success := ec_mul_tmp(success, mulmod(nu, mload(0x0460), R))
                    success := ec_add_acc(success, mload(0x80), mload(0xa0))
                    nu := mulmod(nu, mload(NU_MPTR), R)
                    mstore(0x80, calldataload(0x0724))
                    mstore(0xa0, calldataload(0x0744))
                    for {
                        let mptr := 0x06e4
                        let mptr_end := 0x04e4
                    } lt(mptr_end, mptr) {
                        mptr := sub(mptr, 0x40)
                    } {
                        success := ec_mul_tmp(success, mload(ZETA_MPTR))
                        success := ec_add_tmp(
                            success,
                            calldataload(mptr),
                            calldataload(add(mptr, 0x20))
                        )
                    }
                    success := ec_mul_tmp(success, mulmod(nu, mload(0x0480), R))
                    success := ec_add_acc(success, mload(0x80), mload(0xa0))
                    mstore(0x80, mload(G1_X_MPTR))
                    mstore(0xa0, mload(G1_Y_MPTR))
                    success := ec_mul_tmp(success, sub(R, mload(R_EVAL_MPTR)))
                    success := ec_add_acc(success, mload(0x80), mload(0xa0))
                    mstore(0x80, calldataload(0x11c4))
                    mstore(0xa0, calldataload(0x11e4))
                    success := ec_mul_tmp(success, sub(R, mload(0x0400)))
                    success := ec_add_acc(success, mload(0x80), mload(0xa0))
                    mstore(0x80, calldataload(0x1204))
                    mstore(0xa0, calldataload(0x1224))
                    success := ec_mul_tmp(success, mload(MU_MPTR))
                    success := ec_add_acc(success, mload(0x80), mload(0xa0))
                    mstore(PAIRING_LHS_X_MPTR, mload(0x00))
                    mstore(PAIRING_LHS_Y_MPTR, mload(0x20))
                    mstore(PAIRING_RHS_X_MPTR, calldataload(0x1204))
                    mstore(PAIRING_RHS_Y_MPTR, calldataload(0x1224))
                }
            }

            // Random linear combine with accumulator
            if mload(HAS_ACCUMULATOR_MPTR) {
                mstore(0x00, mload(ACC_LHS_X_MPTR))
                mstore(0x20, mload(ACC_LHS_Y_MPTR))
                mstore(0x40, mload(ACC_RHS_X_MPTR))
                mstore(0x60, mload(ACC_RHS_Y_MPTR))
                mstore(0x80, mload(PAIRING_LHS_X_MPTR))
                mstore(0xa0, mload(PAIRING_LHS_Y_MPTR))
                mstore(0xc0, mload(PAIRING_RHS_X_MPTR))
                mstore(0xe0, mload(PAIRING_RHS_Y_MPTR))
                let challenge := mod(keccak256(0x00, 0x100), r)

                // [pairing_lhs] += challenge * [acc_lhs]
                success := ec_mul_acc(success, challenge)
                success := ec_add_acc(
                    success,
                    mload(PAIRING_LHS_X_MPTR),
                    mload(PAIRING_LHS_Y_MPTR)
                )
                mstore(PAIRING_LHS_X_MPTR, mload(0x00))
                mstore(PAIRING_LHS_Y_MPTR, mload(0x20))

                // [pairing_rhs] += challenge * [acc_rhs]
                mstore(0x00, mload(ACC_RHS_X_MPTR))
                mstore(0x20, mload(ACC_RHS_Y_MPTR))
                success := ec_mul_acc(success, challenge)
                success := ec_add_acc(
                    success,
                    mload(PAIRING_RHS_X_MPTR),
                    mload(PAIRING_RHS_Y_MPTR)
                )
                mstore(PAIRING_RHS_X_MPTR, mload(0x00))
                mstore(PAIRING_RHS_Y_MPTR, mload(0x20))
            }

            // Perform pairing
            success := ec_pairing(
                success,
                mload(PAIRING_LHS_X_MPTR),
                mload(PAIRING_LHS_Y_MPTR),
                mload(PAIRING_RHS_X_MPTR),
                mload(PAIRING_RHS_Y_MPTR)
            )

            // Revert if anything fails
            if iszero(success) {
                revert(0x00, 0x00)
            }

            // Return 1 as result if everything succeeds
            mstore(0x00, 1)
            return(0x00, 0x20)
        }
    }
}
