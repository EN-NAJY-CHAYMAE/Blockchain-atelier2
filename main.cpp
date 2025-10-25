#include <algorithm>
#include <chrono>
#include <cstdint>
#include <cstring>
#include <iomanip>
#include <iostream>
#include <random>
#include <sstream>
#include <string>
#include <vector>
using namespace std;



static inline uint8_t bit_at(const vector<uint8_t>& v, int i) {
    int n = (int)v.size();
    i = (i % n + n) % n;
    return v[i] & 1u;
}

static string to_hex(const vector<uint8_t>& bits) {
    stringstream ss;
    ss << std::hex << std::setfill('0');
    for (size_t i = 0; i < bits.size(); i += 8) {
        uint8_t b = 0;
        for (int k = 0; k < 8; ++k) {
            if (i + k < bits.size() && bits[i + k]) b |= (1u << k);
        }
        ss << setw(2) << (unsigned) b;
    }
    return ss.str();
}

static vector<uint8_t> bytes_to_bits(const vector<uint8_t>& bytes) {
    vector<uint8_t> bits;
    bits.reserve(bytes.size() * 8);
    for (uint8_t c : bytes) {
        for (int k = 0; k < 8; ++k) bits.push_back( (c >> k) & 1u ); 
    }
    return bits;
}

static vector<uint8_t> string_to_bytes(const string& s) {
    return vector<uint8_t>(s.begin(), s.end());
}


// 1.1 init_state():
vector<uint8_t> init_state(const vector<uint8_t>& bits) {             
    vector<uint8_t> s(bits.size());
    for (size_t i = 0; i < bits.size(); ++i) s[i] = bits[i] & 1u;
    return s;
}

// 1.2 evolve(): appliquer la règle de transition.
vector<uint8_t> evolve_once(const vector<uint8_t>& cur, uint32_t rule) { 
    int n = (int)cur.size();
    vector<uint8_t> nxt(n, 0);
    for (int i = 0; i < n; ++i) {
        uint8_t L = bit_at(cur, i - 1);
        uint8_t C = bit_at(cur, i);
        uint8_t R = bit_at(cur, i + 1);
        uint8_t idx = (uint8_t)((L << 2) | (C << 1) | R);
        nxt[i] = (rule >> idx) & 1u;
    }
    return nxt;
}

vector<uint8_t> evolve(vector<uint8_t> state, uint32_t rule, size_t steps) {
    for (size_t t = 0; t < steps; ++t) state = evolve_once(state, rule);
    return state;
}

// 1.3 Vérifier la reproduction correcte sur un petit état initial.
void test_rules_small() {                                            
    vector<uint8_t> init = init_state({0,0,0,1,0,0,0});
    auto r30 = evolve_once(init, 30);
    auto r90 = evolve_once(init, 90);
    auto r110 = evolve_once(init, 110);

    vector<uint8_t> exp30 = {0,0,1,1,1,0,0};
    vector<uint8_t> exp90 = {0,0,1,0,1,0,0};
    vector<uint8_t> exp110= {0,0,1,1,0,0,0};

    auto eq = [](const vector<uint8_t>& a, const vector<uint8_t>& b){
        return a.size()==b.size() && equal(a.begin(),a.end(),b.begin());
    };

    cout << "[Q1.3] Test Rule 30  : " << (eq(r30, exp30)  ? "OK" : "FAIL") << "\n";
    cout << "[Q1.3] Test Rule 90  : " << (eq(r90, exp90)  ? "OK" : "FAIL") << "\n";
    cout << "[Q1.3] Test Rule 110 : " << (eq(r110, exp110) ? "OK" : "FAIL") << "\n";
}

// ===================== 2. Fonction de hachage basée sur l’automate =====================

// - 2.2 Conversion texte→bits : on prend les octets UTF-8 → bits LSB-first.


static vector<uint8_t> pad_to_256_blocks(vector<uint8_t> bits) {        
    bits.push_back(1u);
    while (bits.size() % 256 != 0) bits.push_back(0u);
    return bits;
}

string ac_hash(const std::string& input, uint32_t rule, size_t steps) { 
    // 2.2 conversion texte→bits
    vector<uint8_t> bytes = string_to_bytes(input);
    vector<uint8_t> msg_bits = bytes_to_bits(bytes);
    msg_bits = pad_to_256_blocks(msg_bits);

    vector<uint8_t> S(256, 0);

    for (size_t i = 0; i < msg_bits.size(); i += 256) {
        for (int k = 0; k < 256; ++k) S[k] ^= msg_bits[i + k];
        S = evolve(S, rule, steps);
    }

    return to_hex(S);
}

// Petit test 2.4 : deux entrées différentes donnent deux hashs différents
void test_diff_outputs() {                                               
    string h1 = ac_hash("hello", 110, 8);
    string h2 = ac_hash("hEllo", 110, 8);
    cout << "[Q2.4] hello  -> " << h1 << "\n";
    cout << "[Q2.4] hEllo  -> " << h2 << "\n";
    cout << "[Q2.4] Different? " << (h1 != h2 ? "YES" : "NO (collision)") << "\n";
}





//  SHA-256 minimal  

namespace tinysha256 { 
    using u32 = uint32_t; using u64 = uint64_t; using u8 = uint8_t;

    static inline u32 rotr(u32 x, u32 n){ return (x>>n) | (x<<(32-n)); }
    static inline u32 Ch(u32 x,u32 y,u32 z){ return (x & y) ^ (~x & z); }
    static inline u32 Maj(u32 x,u32 y,u32 z){ return (x & y) ^ (x & z) ^ (y & z); }
    static inline u32 BSIG0(u32 x){ return rotr(x,2)^rotr(x,13)^rotr(x,22); }
    static inline u32 BSIG1(u32 x){ return rotr(x,6)^rotr(x,11)^rotr(x,25); }
    static inline u32 SSIG0(u32 x){ return rotr(x,7)^rotr(x,18)^(x>>3); }
    static inline u32 SSIG1(u32 x){ return rotr(x,17)^rotr(x,19)^(x>>10); }

    static const u32 K[64] = {
        0x428a2f98,0x71374491,0xb5c0fbcf,0xe9b5dba5,0x3956c25b,0x59f111f1,0x923f82a4,0xab1c5ed5,
        0xd807aa98,0x12835b01,0x243185be,0x550c7dc3,0x72be5d74,0x80deb1fe,0x9bdc06a7,0xc19bf174,
        0xe49b69c1,0xefbe4786,0x0fc19dc6,0x240ca1cc,0x2de92c6f,0x4a7484aa,0x5cb0a9dc,0x76f988da,
        0x983e5152,0xa831c66d,0xb00327c8,0xbf597fc7,0xc6e00bf3,0xd5a79147,0x06ca6351,0x14292967,
        0x27b70a85,0x2e1b2138,0x4d2c6dfc,0x53380d13,0x650a7354,0x766a0abb,0x81c2c92e,0x92722c85,
        0xa2bfe8a1,0xa81a664b,0xc24b8b70,0xc76c51a3,0xd192e819,0xd6990624,0xf40e3585,0x106aa070,
        0x19a4c116,0x1e376c08,0x2748774c,0x34b0bcb5,0x391c0cb3,0x4ed8aa4a,0x5b9cca4f,0x682e6ff3,
        0x748f82ee,0x78a5636f,0x84c87814,0x8cc70208,0x90befffa,0xa4506ceb,0xbef9a3f7,0xc67178f2
    };

    struct SHA256 {
        u32 h[8]; u64 bits; vector<u8> buf;
        SHA256(){ reset(); }
        void reset(){
            h[0]=0x6a09e667; h[1]=0xbb67ae85; h[2]=0x3c6ef372; h[3]=0xa54ff53a;
            h[4]=0x510e527f; h[5]=0x9b05688c; h[6]=0x1f83d9ab; h[7]=0x5be0cd19;
            bits=0; buf.clear();
        }
        void process_block(const u8* p){
            u32 w[64];
            for(int i=0;i<16;++i){
                w[i]=(u32)p[4*i]<<24 | (u32)p[4*i+1]<<16 | (u32)p[4*i+2]<<8 | (u32)p[4*i+3];
            }
            for(int i=16;i<64;++i) w[i]=SSIG1(w[i-2])+w[i-7]+SSIG0(w[i-15])+w[i-16];

            u32 a=h[0],b=h[1],c=h[2],d=h[3],e=h[4],f=h[5],g=h[6],hh=h[7];
            for(int i=0;i<64;++i){
                u32 t1=hh+BSIG1(e)+Ch(e,f,g)+K[i]+w[i];
                u32 t2=BSIG0(a)+Maj(a,b,c);
                hh=g; g=f; f=e; e=d+t1; d=c; c=b; b=a; a=t1+t2;
            }
            h[0]+=a; h[1]+=b; h[2]+=c; h[3]+=d; h[4]+=e; h[5]+=f; h[6]+=g; h[7]+=hh;
        }
        void update(const void* data, size_t len){
            const u8* p=(const u8*)data;
            bits += (u64)len*8;
            size_t i=0;
            if(!buf.empty()){
                while(buf.size()<64 && i<len) buf.push_back(p[i++]);
                if(buf.size()==64){ process_block(buf.data()); buf.clear(); }
            }
            while(i+64<=len){ process_block(p+i); i+=64; }
            while(i<len) buf.push_back(p[i++]);
        }
        string final_hex(){
            vector<u8> tmp = buf;
            tmp.push_back(0x80);
            while((tmp.size()+8)%64!=0) tmp.push_back(0x00);
            u64 be = ((bits>>56)&0xff)|(((bits>>48)&0xff)<<8)|(((bits>>40)&0xff)<<16)|(((bits>>32)&0xff)<<24)
                   |(((bits>>24)&0xff)<<32)|(((bits>>16)&0xff)<<40)|(((bits>>8)&0xff)<<48)|((bits&0xff)<<56);
            for(int i=7;i>=0;--i) tmp.push_back((u8)((be>>(8*(7-i)))&0xff));

            for(size_t i=0;i<tmp.size(); i+=64) process_block(tmp.data()+i);

            stringstream ss; ss<<hex<<setfill('0');
            for(int i=0;i<8;++i) ss<<setw(8)<<h[i];
            reset(); 
            return ss.str();
        }
    };

    static inline string sha256_hex(const string& s){
        SHA256 ctx; ctx.update(s.data(), s.size()); return ctx.final_hex();
    }
}
using tinysha256::sha256_hex;

enum class HashMode { SHA256_MODE, AC_HASH_MODE };

struct Block {
    int index{};
    string prevHash;
    string data;
    uint64_t nonce{0};
    uint64_t timestamp{};
    int difficulty{3}; 
    string hash;
};

struct ChainConfig {
    HashMode mode{HashMode::SHA256_MODE};
    uint32_t ac_rule{30};
    size_t   ac_steps{12};
};

static string pow_input(const Block& b){
    string s;
    s += to_string(b.index) + "|";
    s += b.prevHash + "|";
    s += b.data + "|";
    s += to_string(b.timestamp) + "|";
    s += to_string(b.nonce);
    return s;
}

static string compute_block_hash(const Block& b, const ChainConfig& cfg){ 
    string in = pow_input(b);
    if(cfg.mode==HashMode::SHA256_MODE) return sha256_hex(in);
    return ac_hash(in, cfg.ac_rule, cfg.ac_steps);
}

static bool meets_difficulty(const string& hex, int diffNibbles){
    for(int i=0;i<diffNibbles;i++) if(hex[i] != '0') return false;
    return true;
}

struct Blockchain {
    vector<Block> chain;
    ChainConfig cfg;

    explicit Blockchain(ChainConfig c, int difficulty=3){
        cfg = c;
        Block g;
        g.index=0; g.prevHash="GENESIS"; g.data="genesis";
        g.timestamp = (uint64_t)chrono::duration_cast<chrono::seconds>(
            chrono::system_clock::now().time_since_epoch()).count();
        g.difficulty = difficulty;
        while(true){
            g.hash = compute_block_hash(g,cfg);
            if(meets_difficulty(g.hash,g.difficulty)) break;
            ++g.nonce;
        }
        chain.push_back(g);
    }

    uint64_t mine_and_add(const string& data, int difficulty){
        Block b;
        b.index = (int)chain.size();
        b.prevHash = chain.back().hash;
        b.data = data;
        b.timestamp = (uint64_t)chrono::duration_cast<chrono::seconds>(
            chrono::system_clock::now().time_since_epoch()).count();
        b.difficulty = difficulty;
        uint64_t iters = 0;
        while(true){
            ++iters;
            b.hash = compute_block_hash(b,cfg);
            if(meets_difficulty(b.hash,b.difficulty)) break;
            ++b.nonce;
        }
        chain.push_back(b);
        return iters;
    }

    bool validate() const { 
        for(size_t i=1;i<chain.size();++i){
            const Block& cur=chain[i]; const Block& prev=chain[i-1];
            if(cur.prevHash != prev.hash) return false;
            if(!meets_difficulty(cur.hash, cur.difficulty)) return false;
            if(compute_block_hash(cur, ((Blockchain*)this)->cfg) != cur.hash) return false;
        }
        return true;
    }
};

/***************  === 4. Comparaison AC_HASH vs SHA-256  ===  ***************/
struct BenchResult {
    string name;
    double secs_total{};
    double secs_per_block{};
    double avg_iters{};
};

static BenchResult benchmark_mining(HashMode mode, int blocks, int difficulty,
                                    uint32_t rule=30, size_t steps=12){ 
    ChainConfig cfg; cfg.mode=mode; cfg.ac_rule=rule; cfg.ac_steps=steps;
    Blockchain bc(cfg, difficulty);
    auto t0 = chrono::high_resolution_clock::now();
    uint64_t sum_iters=0;
    for(int i=0;i<blocks;i++){
        sum_iters += bc.mine_and_add("tx:"+to_string(i), difficulty);
    }
    auto t1 = chrono::high_resolution_clock::now();
    double secs = chrono::duration<double>(t1-t0).count();
    BenchResult r;
    r.name = (mode==HashMode::SHA256_MODE? "SHA256" : "AC_HASH");
    r.secs_total = secs;
    r.secs_per_block = secs / blocks;
    r.avg_iters = (double)sum_iters/blocks;
    // petite vérif
    cout << "[Q4] Validation ("<<r.name<<"): " << (bc.validate()?"OK":"FAIL") << "\n";
    return r;
}

static void print_bench_table(const BenchResult& a, const BenchResult& b){ // (Q 4.3)
    cout << "\n[Q4.3] Résultats (10 blocs, difficulté fixée)\n";
    cout << "------------------------------------------------------------\n";
    cout << left << setw(12) << "Méthode" 
         << setw(16) << "Temps total (s)"
         << setw(18) << "Temps/bloc (s)"
         << setw(16) << "Iters moy." << "\n";
    cout << "------------------------------------------------------------\n";
    auto row=[&](const BenchResult& x){
        cout << left << setw(12)<<x.name
             << setw(16)<<fixed<<setprecision(4)<<x.secs_total
             << setw(18)<<fixed<<setprecision(6)<<x.secs_per_block
             << setw(16)<<fixed<<setprecision(1)<<x.avg_iters << "\n";
    };
    row(a); row(b);
    cout << "------------------------------------------------------------\n\n";
}

/***************  === 5. Effet avalanche sur ac_hash  ===  ***************/
static vector<uint8_t> hex_to_bits(const string& hex){
    vector<uint8_t> bits; bits.reserve(hex.size()*4);
    auto hv=[&](char c)->int{
        if('0'<=c && c<='9') return c-'0';
        if('a'<=c && c<='f') return 10+(c-'a');
        if('A'<=c && c<='F') return 10+(c-'A');
        return 0;
    };
    for(char c: hex){
        int v=hv(c);
        for(int k=0;k<4;++k) bits.push_back((v>>k)&1);
    }
    return bits;
}

static double avalanche_percent(const string& msg, const ChainConfig& cfg, int trials=64){ 
    std::mt19937_64 rng(42);
    string base = (cfg.mode==HashMode::SHA256_MODE) ? sha256_hex(msg) : ac_hash(msg, cfg.ac_rule, cfg.ac_steps);
    auto bbits = hex_to_bits(base);
    int nbits = (int)bbits.size(); 

    double sumPerc=0.0;
    for(int t=0;t<trials;++t){
        string mutated = msg;
        if(mutated.empty()) mutated.assign(1, '\0');
        size_t pos = rng()%mutated.size();
        uint8_t mask = 1u << (rng()%8);
        mutated[pos] = (char)((uint8_t)mutated[pos] ^ mask);

        string h2 = (cfg.mode==HashMode::SHA256_MODE) ? sha256_hex(mutated)
                                                      : ac_hash(mutated, cfg.ac_rule, cfg.ac_steps);
        auto b2 = hex_to_bits(h2);
        int diff=0;
        for(int i=0;i<nbits;++i) diff += (bbits[i]!=b2[i]);
        sumPerc += 100.0 * diff / nbits;
    }
    return sumPerc / trials;
}

static void run_avalanche_tests(){
    ChainConfig ac; ac.mode=HashMode::AC_HASH_MODE; ac.ac_rule=110; ac.ac_steps=8;
    ChainConfig sh; sh.mode=HashMode::SHA256_MODE;

    string msg = "Avalanche-Test-Message";

    double p_ac  = avalanche_percent(msg, ac, 128);
    double p_sha = avalanche_percent(msg, sh, 128);

    cout << "[Q5.2] Effet avalanche (moyenne % de bits différents)\n";
    cout << "  AC_HASH (Rule "<<ac.ac_rule<<", steps "<<ac.ac_steps<<"): " << fixed<<setprecision(2)<<p_ac << "%\n";
    cout << "  SHA-256: " << fixed<<setprecision(2)<<p_sha << "%\n\n";
}

/***************  === 6. Distribution des bits produits par ac_hash  ===  ***************/
static void bit_distribution(HashMode mode, uint32_t rule, size_t steps, size_t min_bits=100000){ 
    ChainConfig cfg; cfg.mode=mode; cfg.ac_rule=rule; cfg.ac_steps=steps;
    std::mt19937_64 rng(1337);
    size_t bits_count=0; size_t ones=0; size_t samples=0;

    while(bits_count < min_bits){
        size_t L = 16 + (rng()%33);
        string m; m.resize(L);
        for(size_t i=0;i<L;++i) m[i] = (char)(rng() & 0xFF);

        string h = (mode==HashMode::SHA256_MODE) ? sha256_hex(m) : ac_hash(m, rule, steps);
        auto b = hex_to_bits(h);
        for(uint8_t bit : b){ ones += bit; }
        bits_count += b.size();
        ++samples;
    }
    double p1 = 100.0 * ones / bits_count;
    cout << "[Q6] Distribution des bits ("<<(mode==HashMode::SHA256_MODE?"SHA256":"AC_HASH")
         <<", Rule "<<rule<<", steps "<<steps<<")\n";
    cout << "  Bits analysés: " << bits_count << "  (échantillons="<<samples<<")\n";
    cout << "  Pourcentage de '1' : " << fixed<<setprecision(2)<<p1 << " %  --> "
         << ((p1>47.0 && p1<53.0) ? "≈ ÉQUILIBRÉ" : "déséquilibré") << "\n\n";
}

/***************  === 7. Tests multi-règles d’automate  ===  ***************/
static void compare_rules(){
    vector<uint32_t> rules = {30, 90, 110};
    size_t steps = 8;


    string msg="Rules-Comparison-Message";
    for(uint32_t r : rules){
        ChainConfig cfg; cfg.mode=HashMode::AC_HASH_MODE; cfg.ac_rule=r; cfg.ac_steps=steps;
        auto t0=chrono::high_resolution_clock::now();
        for(int i=0;i<500;++i){ (void)ac_hash(msg+to_string(i), r, steps); }
        auto t1=chrono::high_resolution_clock::now();
        double secs = chrono::duration<double>(t1-t0).count();

        double aval = avalanche_percent(msg, cfg, 128);

        cout << "[Q7] Rule "<<setw(3)<<r<<" | steps "<<steps
             << " | temps 500 hashs: "<<fixed<<setprecision(3)<<secs<<" s"
             << " | avalanche: "<<fixed<<setprecision(2)<<aval<<" %\n";
    }
    cout << "\n[Q7] Remarque: règle \"meilleure\" pour hachage = bon compromis "
            "entre (i) diffusion élevée (avalanche ~50%) et (ii) vitesse.\n\n";
}




// ===================== Q8 — Avantages (texte) =====================
static void q8_print_advantages() {
    cout << "===== Q8 — Avantages potentiels d’un hash AC en blockchain =====\n";
    cout << "1) Simplicite & performance: regles locales (voisinage r=1), operations bitwise => rapide, facile a paralleliser.\n";
    cout << "2) Implementation legere: code court, sans tables lourdes; bon pour environnements embarques.\n";
    cout << "3) Diffusion par iterations: petites entrees se propagent vite (bonne sensibilite aux conditions initiales).\n";
    cout << "4) Parametrable: regle (30/90/110...), nb d’iterations, taille d’etat => ajustable selon besoins.\n";
    cout << "5) Entropie visuelle: certains ECA (ex. Rule 30) generent des motifs pseudo-aleatoires interessants.\n\n";
}

// ===================== Q9 — Faiblesses / Vulnerabilites (texte) =====================
static void q9_print_weaknesses() {
    cout << "===== Q9 — Faiblesses / Vulnerabilites possibles =====\n";
    cout << "1) Analyse cryptographique limitee: ECA classiques peu etudies / standardises vs SHA-2/3.\n";
    cout << "2) Reglage sensible: certaines regles/parametres peuvent produire des sorties moins uniformes.\n";
    cout << "3) Structure lineaire potentielle: quelques regles lineaires (ex. 90) => attaques algebraiques possibles.\n";
    cout << "4) Collisions/preimage: pas de preuves formelles; AC_HASH doit etre combine/renforce pour production.\n";
    cout << "5) Interoperabilite: pas de support natif/acceleration materielle comme SHA/Blake.\n\n";
}

// ===================== Q10 — Amelioration / Variante =====================
static string ac_sha256_combo(const string& msg, uint32_t rule, size_t steps) {
    string h_ac  = ac_hash(msg, rule, steps);       
    string h_sha = tinysha256::sha256_hex(msg);         
    return tinysha256::sha256_hex(h_ac + h_sha);        
}

static void q10_print_improvement_demo() {
    cout << "===== Q10 — Variante: COMBINE = SHA256( AC_HASH(m) || SHA256(m) ) =====\n";
    string m = "Variant-Demo";
    string h = ac_sha256_combo(m, /*rule*/110, /*steps*/8);
    cout << "Input  : " << m << "\n";
    cout << "Output : " << h << " (256 bits)\n";
    cout << "Raison : combine diffusion AC + securite SHA256; si l’un est fragilise, l’autre renforce.\n\n";
}

// ===================== Q11 — Tableau de resultats (hashs, temps, avalanche, uniformite) =====================
static double bit_one_ratio(HashMode mode, uint32_t rule, size_t steps, size_t min_bits = 100000) {
    ChainConfig cfg; cfg.mode = mode; cfg.ac_rule = rule; cfg.ac_steps = steps;
    std::mt19937_64 rng(1337);
    size_t bits=0, ones=0;
    while (bits < min_bits) {
        size_t L = 16 + (rng()%33);
        string m; m.resize(L);
        for (size_t i=0;i<L;++i) m[i] = (char)(rng() & 0xFF);
        string h = (mode==HashMode::SHA256_MODE) ? tinysha256::sha256_hex(m) : ac_hash(m, rule, steps);
        auto b = hex_to_bits(h);
        for (auto v: b) ones += v;
        bits += b.size();
    }
    return 100.0 * ones / bits;
}

static void q11_results_table() {
    cout << "===== Q11 — Tableau de synthese (mesures rapides) =====\n";
    const int blocks = 5, difficulty = 2;
    const uint32_t rule = 110; const size_t steps = 8;

    auto R_sha = benchmark_mining(HashMode::SHA256_MODE, blocks, difficulty);
    auto R_ac  = benchmark_mining(HashMode::AC_HASH_MODE,  blocks, difficulty, rule, steps);

    ChainConfig cSHA; cSHA.mode = HashMode::SHA256_MODE;
    ChainConfig cAC;  cAC.mode  = HashMode::AC_HASH_MODE; cAC.ac_rule = rule; cAC.ac_steps = steps;
    string probe = "Q11-probe";
    double A_sha = avalanche_percent(probe, cSHA, 32);
    double A_ac  = avalanche_percent(probe, cAC,  32);

    // Uniformite (% de 1)
    double U_sha = bit_one_ratio(HashMode::SHA256_MODE, 0, 0, 32768);
    double U_ac  = bit_one_ratio(HashMode::AC_HASH_MODE, rule, steps, 32768);

    cout << left << setw(10) << "Methode"
         << setw(16) << "Temps_total(s)"
         << setw(16) << "Temps/bloc(s)"
         << setw(14) << "Iters_moy"
         << setw(12) << "Aval(%)"
         << setw(12) << "%1_bits"
         << "\n";
    cout << string(80, '-') << "\n";
    auto row = [&](const BenchResult& B, double aval, double ones, const string& name){
        cout << left << setw(10) << name
             << setw(16) << fixed << setprecision(4) << B.secs_total
             << setw(16) << fixed << setprecision(6) << B.secs_per_block
             << setw(14) << fixed << setprecision(1) << B.avg_iters
             << setw(12) << fixed << setprecision(2) << aval
             << setw(12) << fixed << setprecision(2) << ones
             << "\n";
    };
    row(R_sha, A_sha, U_sha, "SHA256");
    row(R_ac,  A_ac,  U_ac,  "AC_HASH");
    cout << "\n";
}

// ===================== Q12 — Mode d’execution automatique =====================
static void run_all_sections_fast() {
    test_rules_small();
    test_diff_outputs();
    ChainConfig cfgAC; cfgAC.mode=HashMode::AC_HASH_MODE; cfgAC.ac_rule=110; cfgAC.ac_steps=8;
    Blockchain bc(cfgAC, 2);
    bc.mine_and_add("b1", 2); bc.mine_and_add("b2", 2);
    cout << "[Q3.3] validate(): " << (bc.validate() ? "OK" : "FAIL") << "\n\n";

    auto rsha=benchmark_mining(HashMode::SHA256_MODE, 5, 2);
    auto rac =benchmark_mining(HashMode::AC_HASH_MODE,  5, 2, 110, 8);
    print_bench_table(rsha, rac);

    run_avalanche_tests();
    bit_distribution(HashMode::AC_HASH_MODE, 110, 8, 32768);
    bit_distribution(HashMode::SHA256_MODE,  0,   0, 32768);
    compare_rules();

    // Q8–Q12
    q8_print_advantages();
    q9_print_weaknesses();
    q10_print_improvement_demo();
    q11_results_table();
    cout << "===== Q12 — Mode auto termine (utiliser: --auto) =====\n\n";
}


int main(int argc, char** argv) {
    ios::sync_with_stdio(false);
    cin.tie(nullptr);

    vector<string> args(argv+1, argv+argc);

    // Tiny CLI
    if (args.size() >= 2 && args[0] == "--run") {
        string what = args[1];
        if (what == "Q1") { test_rules_small(); }
        else if (what == "Q2") { test_diff_outputs(); }
        else if (what == "Q3") {
            ChainConfig cfgAC; cfgAC.mode=HashMode::AC_HASH_MODE; cfgAC.ac_rule=110; cfgAC.ac_steps=8;
            Blockchain bc(cfgAC, 3);
            bc.mine_and_add("block-1 data", 3);
            bc.mine_and_add("block-2 data", 3);
            cout << "[Q3.3] validate(): " << (bc.validate() ? "OK" : "FAIL") << "\n\n";
        }
        else if (what == "Q4") {
            auto rsha=benchmark_mining(HashMode::SHA256_MODE,10,3);
            auto rac =benchmark_mining(HashMode::AC_HASH_MODE,10,3,110,8);
            print_bench_table(rsha, rac);
        }
        else if (what == "Q5") { run_avalanche_tests(); }
        else if (what == "Q6") {
            bit_distribution(HashMode::AC_HASH_MODE,110,8,100000);
            bit_distribution(HashMode::SHA256_MODE,  0,  0,100000);
        }
        else if (what == "Q7") { compare_rules(); }
        else if (what == "Q8") { q8_print_advantages(); }
        else if (what == "Q9") { q9_print_weaknesses(); }
        else if (what == "Q10"){ q10_print_improvement_demo(); }
        else if (what == "Q11"){ q11_results_table(); }
        else if (what == "Q12"){ run_all_sections_fast(); }
        else { cout << "Unknown part. Use Q1..Q12 or --auto.\n"; }
        return 0;
    }
    if (args.size() == 1 && args[0] == "--auto") {
        run_all_sections_fast();
        return 0;
    }

    test_rules_small();
    test_diff_outputs();

    cout << "[DEMO] Rule=30, steps=12\n";
    cout << "Input : Blockchain TP - Automate Cellulaire\n";
    cout << "Hash  : " << ac_hash("Blockchain TP - Automate Cellulaire", 30, 12) << " (256 bits)\n\n";

    ChainConfig cfgAC; cfgAC.mode=HashMode::AC_HASH_MODE; cfgAC.ac_rule=110; cfgAC.ac_steps=8;
    Blockchain bc(cfgAC, 3);
    bc.mine_and_add("block-1 data", 3);
    bc.mine_and_add("block-2 data", 3);
    cout << "[Q3.3] validate(): " << (bc.validate() ? "OK" : "FAIL") << "\n\n";

    auto r_sha = benchmark_mining(HashMode::SHA256_MODE, 10, 3);
    auto r_ac  = benchmark_mining(HashMode::AC_HASH_MODE,  10, 3, 110, 8);
    print_bench_table(r_sha, r_ac);

    run_avalanche_tests();
    bit_distribution(HashMode::AC_HASH_MODE, 110, 8, 100000);
    bit_distribution(HashMode::SHA256_MODE,  0,   0, 100000);
    compare_rules();

    // Q8–Q12 default run
    q8_print_advantages();
    q9_print_weaknesses();
    q10_print_improvement_demo();
    q11_results_table();
    cout << "===== Q12 — Pour tout generer automatiquement: --auto =====\n\n";

    return 0;
}


// int main() {
//     ios::sync_with_stdio(false);
//     cin.tie(nullptr);

//     // Q1.3 – Vérification des règles de base sur petit état
//     test_rules_small();

//     // Q2.4 – Test de non-égalité des hashs
//     test_diff_outputs();

//     // Démo libre: calcul d’un hash sur une phrase, avec Rule 30 et 12 itérations
//     string demo = "Blockchain TP - Automate Cellulaire";
//     string H = ac_hash(demo, /*rule*/30, /*steps*/12);
//     cout << "[DEMO] Rule=30, steps=12\n";
//     cout << "Input : " << demo << "\n";
//     cout << "Hash  : " << H << " (256 bits)\n";
//     return 0;
// }
