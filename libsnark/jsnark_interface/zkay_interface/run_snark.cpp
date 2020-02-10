//
// Created by nicbauma on 31.10.19.
//

#include <libsnark/zk_proof_systems/ppzksnark/r1cs_se_ppzksnark/r1cs_se_ppzksnark.hpp>
#include <libsnark/common/default_types/r1cs_se_ppzksnark_pp.hpp>
#include <libsnark/jsnark_interface/CircuitReader.hpp>

enum ProvingScheme {
    GM17
};

// External interface
extern "C" {
int generate_keys(const char *circuit_output_dir, int proving_scheme);
int generate_proof(const char *circuit_output_dir, const char *input_file, int proving_scheme, int check_verification);
}

template<typename ppT>
static string serialize(libff::G1<ppT> pt) {
    size_t num_limbs = libff::alt_bn128_Fq::num_limbs;
    pt.to_affine_coordinates();
    char buf[256];
    gmp_snprintf(buf, 256, "%#Nx\n%#Nx\n", pt.X.as_bigint().data, num_limbs, pt.Y.as_bigint().data, num_limbs);
    return string(buf);
}

template<typename ppT>
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
void writeToFile(const std::string &path, const T &obj) {
    std::ofstream fh(path, std::ios::binary);
    fh << obj;
}

template<typename T>
T loadFromFile(const std::string &path) {
    std::ifstream fh(path, std::ios::binary);
    T obj;
    fh >> obj;
    return obj;
}

template<typename ppT>
static void generate_keys_gm17(const r1cs_constraint_system<FieldT> &cs,
                               const std::string &prover_key_filename,
                               const std::string &verification_key_filename) {
    // Generate keypair
    r1cs_se_ppzksnark_keypair<ppT> keypair = r1cs_se_ppzksnark_generator<ppT>(cs);

    // Dump proving key to binary file
    libff::enter_block("WritingProverKey");
    writeToFile(prover_key_filename, keypair.pk);
    libff::leave_block("WritingProverKey");

    // Dump verification key in text format
    libff::enter_block("SerializeVk");
    ofstream vk_out(verification_key_filename);
    const auto &vk = keypair.vk;
    vk_out << serialize<ppT>(vk.H);
    vk_out << serialize<ppT>(vk.G_alpha);
    vk_out << serialize<ppT>(vk.H_beta);
    vk_out << serialize<ppT>(vk.G_gamma);
    vk_out << serialize<ppT>(vk.H_gamma);
    vk_out << vk.query.size() << endl;
    for (const libff::G1<ppT> &q : keypair.vk.query) {
        vk_out << serialize<ppT>(q);
    }
    libff::leave_block("SerializeVk");

    // Also dump in binary format for local verification
    writeToFile(verification_key_filename + ".bin", vk);
}

template<typename ppT>
static bool generate_proof_gm17(const r1cs_primary_input<FieldT> &public_inputs,
                                const r1cs_auxiliary_input<FieldT> &private_inputs,
                                const std::string &prover_key_filename,
                                const std::string &verification_key_filename,
                                const std::string &proof_filename,
                                bool check_verification) {

    r1cs_se_ppzksnark_proof<ppT> proof;
    {
        // Read proving key
        libff::enter_block("ReadingProverKey");
        r1cs_se_ppzksnark_proving_key<ppT> pk = loadFromFile<r1cs_se_ppzksnark_proving_key<ppT>>(prover_key_filename);
        libff::leave_block("ReadingProverKey");

        // Generate proof
        proof = r1cs_se_ppzksnark_prover<ppT>(pk, public_inputs, private_inputs);
    }

    // Dump proof in text format
    libff::enter_block("SerializeProof");
    ofstream p(proof_filename);
    p << serialize<ppT>(proof.A);
    p << serialize<ppT>(proof.B);
    p << serialize<ppT>(proof.C);
    libff::leave_block("SerializeProof");

    if (check_verification) {
        // Check if verification works
        r1cs_se_ppzksnark_verification_key<ppT> vk =
                loadFromFile<r1cs_se_ppzksnark_verification_key<ppT>>(verification_key_filename);

        libff::print_header("R1CS SEppzkSNARK Verifier");
        const bool ans = r1cs_se_ppzksnark_verifier_strong_IC<ppT>(vk, public_inputs, proof);
        printf("\n");
        libff::print_indent();
        libff::print_mem("after verifier");
        printf("* The verification result is: %s\n", (ans ? "PASS" : "FAIL"));
        if (!ans) {
            return false;
        }
    }

    return true;
}

int generate_keys(const char *circuit_output_dir, int proving_scheme) {
    libff::start_profiling();
    gadgetlib2::initPublicParamsFromDefaultPp();
    gadgetlib2::GadgetLibAdapter::resetVariableIndex();

    auto ps = static_cast<ProvingScheme>(proving_scheme);
    const string out_dir(circuit_output_dir);

    const string arith_filename = out_dir + "/circuit.arith";
    const string dummy_input_filename = out_dir + "/circuit.in";
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
        case ProvingScheme::GM17:
            libff::print_header("GM17 Generator");
            generate_keys_gm17<libsnark::default_r1cs_se_ppzksnark_pp>(cs, prover_key_filename,
                                                                       verification_key_filename);
            break;
        default:
            return -1;
    }

    return 0;
}

int generate_proof(const char *circuit_output_dir, const char *input_file, int proving_scheme, int check_verification) {
    libff::start_profiling();
    gadgetlib2::initPublicParamsFromDefaultPp();
    gadgetlib2::GadgetLibAdapter::resetVariableIndex();

    auto ps = static_cast<ProvingScheme>(proving_scheme);
    const string out_dir(circuit_output_dir);

    const string arith_filename = out_dir + "/circuit.arith";
    const string prover_key_filename = out_dir + "/proving.key";
    const string verification_key_filename = out_dir + "/verification.key.bin";
    const string proof_filename = out_dir + "/proof.out";

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
                    CircuitReader reader(arith_filename.c_str(), input_file, pb);
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

    switch (ps) {
        case ProvingScheme::GM17: {
            libff::print_header("GM17 Prover");
            bool ret = generate_proof_gm17<libsnark::default_r1cs_se_ppzksnark_pp>(primary_input, auxiliary_input,
                                                                                   prover_key_filename,
                                                                                   verification_key_filename,
                                                                                   proof_filename,
                                                                                   check_verification);
            if (!ret) return -2;
            break;
        }
        default:
            return -1;
    }

    return 0;
}

int main(int argc, char **argv) {
    if (argc == 3 && strcmp("keygen", argv[1]) == 0) {
        return generate_keys(".", stoi(string(argv[2])));
    } else if (argc == 4 && strcmp("proofgen", argv[1]) == 0) {
        return generate_proof(".", "circuit.in", stoi(string(argv[2])), stoi(string(argv[3])));
    }
    cerr << "Invalid command" << endl;
    return -1;
}