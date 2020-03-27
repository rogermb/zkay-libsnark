//
// Created by nicbauma on 31.10.19.
//

#include <libsnark/zk_proof_systems/ppzksnark/r1cs_ppzksnark/r1cs_ppzksnark.hpp>
#include <libsnark/zk_proof_systems/ppzksnark/r1cs_gg_ppzksnark/r1cs_gg_ppzksnark.hpp>
#include <libsnark/zk_proof_systems/ppzksnark/r1cs_se_ppzksnark/r1cs_se_ppzksnark.hpp>

#include <libsnark/jsnark_interface/CircuitReader.hpp>

enum ProvingScheme {
    PGHR13,
    GROTH16,
    GM17
};

// External interface
extern "C" {
int generate_keys(const char *input_directory, const char *output_directory, int proving_scheme);
int generate_proof(const char *keys_dir, const char *input_dir, const char *output_filename, int proving_scheme, int check_verification);
}

using ppT = libff::default_ec_pp;

static string serialize(libff::G1<ppT> pt) {
    size_t num_limbs = libff::alt_bn128_Fq::num_limbs;
    pt.to_affine_coordinates();
    char buf[256];
    gmp_snprintf(buf, 256, "%#Nx\n%#Nx\n", pt.X.as_bigint().data, num_limbs, pt.Y.as_bigint().data, num_limbs);
    return string(buf);
}

static string serialize(libff::G2<ppT> pt) {
    size_t num_limbs = libff::alt_bn128_Fq::num_limbs;
    pt.to_affine_coordinates();
    char buf[512];
    gmp_snprintf(buf, 512, "%#Nx\n%#Nx\n%#Nx\n%#Nx\n",
                 pt.X.c1.as_bigint().data, num_limbs, pt.X.c0.as_bigint().data, num_limbs,
                 pt.Y.c1.as_bigint().data, num_limbs, pt.Y.c0.as_bigint().data, num_limbs);
    return string(buf);
}

template<typename T>
static void writeToFile(const std::string &path, const T &obj) {
    std::ofstream fh(path, std::ios::binary);
    fh << obj;
}

template<typename T>
static T loadFromFile(const std::string &path) {
    std::ifstream fh(path, std::ios::binary);
    T obj;
    fh >> obj;
    return obj;
}

static void serialize_vk(std::ofstream &vk_out, const r1cs_ppzksnark_verification_key<ppT> &vk,
                         const r1cs_ppzksnark_proving_key<ppT> &) {
    vk_out << serialize(vk.alphaA_g2);
    vk_out << serialize(vk.alphaB_g1);
    vk_out << serialize(vk.alphaC_g2);
    vk_out << serialize(vk.gamma_g2);
    vk_out << serialize(vk.gamma_beta_g1);
    vk_out << serialize(vk.gamma_beta_g2);
    vk_out << serialize(vk.rC_Z_g2);

    const auto &IC = vk.encoded_IC_query;
    vk_out << IC.size() + 1 << endl;
    vk_out << serialize(IC.first);
    for (size_t i = 0; i < IC.size(); i++) {
        auto IC_N(IC.rest[i]);
        vk_out << serialize(IC_N);
    }
}

static void serialize_vk(std::ofstream &vk_out, const r1cs_gg_ppzksnark_verification_key<ppT> &vk,
                         const r1cs_gg_ppzksnark_proving_key<ppT> &pk) {
    vk_out << serialize(pk.alpha_g1);
    vk_out << serialize(pk.beta_g2);
    vk_out << serialize(vk.gamma_g2);
    vk_out << serialize(vk.delta_g2);

    const auto &abc = vk.gamma_ABC_g1;
    vk_out << abc.size() + 1 << endl;
    vk_out << serialize(abc.first);
    for (size_t i = 0; i < abc.size(); i++) {
        auto abc_n(abc.rest[i]);
        vk_out << serialize(abc_n);
    }
}

static void serialize_vk(std::ofstream &vk_out, const r1cs_se_ppzksnark_verification_key<ppT> &vk,
                         const r1cs_se_ppzksnark_proving_key<ppT> &) {
    vk_out << serialize(vk.H);
    vk_out << serialize(vk.G_alpha);
    vk_out << serialize(vk.H_beta);
    vk_out << serialize(vk.G_gamma);
    vk_out << serialize(vk.H_gamma);

    vk_out << vk.query.size() << endl;
    for (const libff::G1<ppT> &q : vk.query) {
        vk_out << serialize(q);
    }
}

static void serialize_proof(std::ofstream &p_out, const r1cs_ppzksnark_proof<ppT> &p) {
    p_out << serialize(p.g_A.g);
    p_out << serialize(p.g_A.h);
    p_out << serialize(p.g_B.g);
    p_out << serialize(p.g_B.h);
    p_out << serialize(p.g_C.g);
    p_out << serialize(p.g_C.h);
    p_out << serialize(p.g_K);
    p_out << serialize(p.g_H);
}

static void serialize_proof(std::ofstream &p_out, const r1cs_gg_ppzksnark_proof<ppT> &p) {
    p_out << serialize(p.g_A);
    p_out << serialize(p.g_B);
    p_out << serialize(p.g_C);
}

static void serialize_proof(std::ofstream &p_out, const r1cs_se_ppzksnark_proof<ppT> &p) {
    p_out << serialize(p.A);
    p_out << serialize(p.B);
    p_out << serialize(p.C);
}

template<typename KeyPairT, KeyPairT (*generate)(const r1cs_constraint_system<FieldT> &)>
static void keygen(const r1cs_constraint_system<FieldT> &cs,
                   const std::string &prover_key_filename,
                   const std::string &verification_key_filename) {
    // Generate keypair
    auto keypair = generate(cs);

    // Dump proving key to binary file
    libff::enter_block("WritingProverKey");
    writeToFile(prover_key_filename, keypair.pk);
    libff::leave_block("WritingProverKey");

    // Dump verification key in text format
    libff::enter_block("SerializeVk");
    ofstream vk_out(verification_key_filename);
    serialize_vk(vk_out, keypair.vk, keypair.pk);
    libff::leave_block("SerializeVk");

    // Also dump in binary format for local verification
    writeToFile(verification_key_filename + ".bin", keypair.vk);
}

template<typename ProofT, typename ProvingKeyT,
        ProofT (*prove)(const ProvingKeyT &, const r1cs_primary_input<FieldT> &, const r1cs_auxiliary_input<FieldT> &),
        typename VerificationKeyT,
        bool (*verify)(const VerificationKeyT &, const r1cs_primary_input<FieldT> &, const ProofT &)>
static bool proofgen(const r1cs_primary_input<FieldT> &public_inputs,
                     const r1cs_auxiliary_input<FieldT> &private_inputs,
                     const std::string &prover_key_filename,
                     const std::string &verification_key_filename,
                     const std::string &proof_filename,
                     bool check_verification) {

    ProofT proof;
    {
        // Read proving key
        libff::enter_block("ReadingProverKey");
        auto pk = loadFromFile<ProvingKeyT>(prover_key_filename);
        libff::leave_block("ReadingProverKey");

        // Generate proof
        proof = prove(pk, public_inputs, private_inputs);
    }

    // Dump proof in text format
    libff::enter_block("SerializeProof");
    ofstream p(proof_filename);
    serialize_proof(p, proof);
    libff::leave_block("SerializeProof");

    if (check_verification) {
        // Check if verification works
        auto vk = loadFromFile<VerificationKeyT>(verification_key_filename);

        libff::enter_block("Verifying proof");
        const bool ans = verify(vk, public_inputs, proof);
        printf("\n");
        printf("* The verification result is: %s\n", (ans ? "PASS" : "FAIL"));
        libff::leave_block("Verifying proof");
        return ans;
    }
    return true;
}

int generate_keys(const char *input_directory, const char *output_directory, int proving_scheme) {
    libff::start_profiling();
    gadgetlib2::initPublicParamsFromDefaultPp();
    gadgetlib2::GadgetLibAdapter::resetVariableIndex();

    auto ps = static_cast<ProvingScheme>(proving_scheme);
    const string in_dir(input_directory);
    const string out_dir(output_directory);

    const string arith_filename = in_dir + "/circuit.arith";
    const string dummy_input_filename = in_dir + "/circuit.in";
    const string prover_key_filename = out_dir + "/proving.key";
    const string verification_key_filename = out_dir + "/verification.key";

    // Read the circuit, evaluate, and translate constraints
    r1cs_constraint_system<FieldT> cs;
    {
        ProtoboardPtr pb = gadgetlib2::Protoboard::create(gadgetlib2::R1P);
        libff::enter_block("CircuitReading");
        CircuitReader reader(arith_filename.c_str(), dummy_input_filename.c_str(), pb);
        libff::leave_block("CircuitReading");
        libff::enter_block("Extract constraint system");
        cs = get_constraint_system_from_gadgetlib2(*pb);
        cs.primary_input_size = reader.getNumInputs() + reader.getNumOutputs();
        cs.auxiliary_input_size = gadgetlib2::GadgetLibAdapter::getNextFreeIndex() - cs.num_inputs();
        libff::leave_block("Extract constraint system");
    }

    switch (ps) {
        case ProvingScheme::PGHR13:
            libff::print_header("PGHR13 Generator");
            keygen<r1cs_ppzksnark_keypair<ppT>, r1cs_ppzksnark_generator<ppT>>(cs, prover_key_filename,
                                                                               verification_key_filename);
            break;
        case ProvingScheme::GROTH16:
            libff::print_header("Groth16 Generator");
            keygen<r1cs_gg_ppzksnark_keypair<ppT>, r1cs_gg_ppzksnark_generator<ppT>>(cs, prover_key_filename,
                                                                                     verification_key_filename);
            break;
        case ProvingScheme::GM17:
            libff::print_header("GM17 Generator");
            keygen<r1cs_se_ppzksnark_keypair<ppT>, r1cs_se_ppzksnark_generator<ppT>>(cs, prover_key_filename,
                                                                                     verification_key_filename);
            break;
        default:
            return -1;
    }

    return 0;
}

int generate_proof(const char *keys_dir, const char *input_dir, const char *output_filename, int proving_scheme, int check_verification) {
    libff::start_profiling();
    gadgetlib2::initPublicParamsFromDefaultPp();
    gadgetlib2::GadgetLibAdapter::resetVariableIndex();

    auto ps = static_cast<ProvingScheme>(proving_scheme);
    const string in_dir(input_dir);
    const string key_dir(keys_dir);

    const string arith_filename = in_dir + "/circuit.arith";
    const string in_filename = in_dir + "/circuit.in";
    const string prover_key_filename = key_dir + "/proving.key";
    const string verification_key_filename = key_dir + "/verification.key.bin";

    r1cs_primary_input<FieldT> primary_input;
    r1cs_auxiliary_input<FieldT> auxiliary_input;
    {
        r1cs_constraint_system<FieldT> cs;
        {
            // Read the circuit, evaluate, and translate constraints
            libff::enter_block("CircuitReading");
            r1cs_variable_assignment<FieldT> full_assignment;
            {
                ProtoboardPtr pb = gadgetlib2::Protoboard::create(gadgetlib2::R1P);
                size_t primary_input_size;
                {
                    CircuitReader reader(arith_filename.c_str(), in_filename.c_str(), pb);
                    primary_input_size = reader.getNumInputs() + reader.getNumOutputs();
                }
                cs = get_constraint_system_from_gadgetlib2(*pb);
                full_assignment = get_variable_assignment_from_gadgetlib2(*pb);
                cs.primary_input_size = primary_input_size;
                cs.auxiliary_input_size = full_assignment.size() - primary_input_size;
                libff::leave_block("CircuitReading");
            }

            // extract primary and auxiliary input
            primary_input.assign(full_assignment.begin(), full_assignment.begin() + cs.num_inputs());
            auxiliary_input.assign(full_assignment.begin() + cs.num_inputs(), full_assignment.end());
        }

        if (!cs.is_satisfied(primary_input, auxiliary_input)) {
            cout << "The constraint system is not satisfied by the value assignment - Terminating." << endl;
            return -2;
        }
    }

    bool ret;
    switch (ps) {
        case ProvingScheme::PGHR13: {
            libff::print_header("PGHR13 Prover");
            ret = proofgen<
                    r1cs_ppzksnark_proof<ppT>, r1cs_ppzksnark_proving_key<ppT>, r1cs_ppzksnark_prover<ppT>,
                    r1cs_ppzksnark_verification_key<ppT>, r1cs_ppzksnark_verifier_strong_IC<ppT>>(
                            primary_input, auxiliary_input, prover_key_filename, verification_key_filename, output_filename,
                            check_verification
            );
            break;
        }
        case ProvingScheme::GROTH16: {
            libff::print_header("Groth16 Prover");
            ret = proofgen<
                    r1cs_gg_ppzksnark_proof<ppT>, r1cs_gg_ppzksnark_proving_key<ppT>, r1cs_gg_ppzksnark_prover<ppT>,
                    r1cs_gg_ppzksnark_verification_key<ppT>, r1cs_gg_ppzksnark_verifier_strong_IC<ppT>>(
                            primary_input, auxiliary_input, prover_key_filename, verification_key_filename, output_filename,
                            check_verification
            );
            break;
        }
        case ProvingScheme::GM17: {
            libff::print_header("GM17 Prover");
            ret = proofgen<
                    r1cs_se_ppzksnark_proof<ppT>, r1cs_se_ppzksnark_proving_key<ppT>, r1cs_se_ppzksnark_prover<ppT>,
                    r1cs_se_ppzksnark_verification_key<ppT>, r1cs_se_ppzksnark_verifier_strong_IC<ppT>>(
                            primary_input, auxiliary_input, prover_key_filename, verification_key_filename, output_filename,
                            check_verification
            );
            break;
        }
        default:
            return -1;
    }
    if (!ret) return -2;

    return 0;
}

int main(int argc, char **argv) {
    if (argc >= 5) {
        const char *in_dir = argv[2];
        const char *out_path = argv[3];
        if (argc == 5 && strcmp("keygen", argv[1]) == 0) {
            return generate_keys(in_dir, out_path, stoi(string(argv[4])));
        } else if (argc == 7 && strcmp("proofgen", argv[1]) == 0) {
            const char *key_dir = argv[4];
            return generate_proof(key_dir, in_dir, out_path, stoi(string(argv[5])), stoi(string(argv[6])));
        }
    }
    cerr << "Invalid command" << endl;
    return -1;
}