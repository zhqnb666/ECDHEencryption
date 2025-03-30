#include <iostream>
#include <cstdio>
#include <cstdint>
#include <cstring>
#include <cassert>
using namespace std;
#define GET_BIT(x, i) (((x) >> (i)) & 1)
#define SET_BIT(x, i, v) ((x) = ((x) & ~(1 << (i))) | ((v & 1) << (i)))
#define COPY_BIT(x, i, y, j) SET_BIT(x, i, GET_BIT(y, j))
#define PERMUTE(x, p, n) ({ \
    uint16_t res = 0; \
    for (int i = 0; i < n; ++i) { \
        SET_BIT(res, i, GET_BIT(x, p[i])); \
    } \
    res; \
})
#define BIN_NUM(b1, b0) (((b1) << 1) | (b0))
#define CONCAT(x, y) (((x) << 4) | (y))
#define Theta(x) ((((x) >> 4) & 0x0F) | (((x) & 0x0F) << 4))
typedef long long ll;
const int L = 1e6 + 5;
ll a, b, p, x_g, y_g; // The parameters of an elliptic curve and the generator point G = (x_g, y_g)
char msgRcv[L], msgSnd[L], cipherText[L];
int cnt[256];

struct Mod {
    ll val;
    Mod() : val(0) {}
    Mod(ll v) {
        val = v % p;
        if (val < 0) val += p;
    }
    Mod operator+(const Mod &b) const {
        return Mod(val + b.val);
    }
    Mod operator+(ll b) const {
        return Mod(val + b);
    }
    Mod operator-(const Mod &b) const {
        return Mod(val - b.val);
    }
    Mod operator*(const Mod &b) const {
        return Mod(val * b.val);
    }
    Mod operator*(ll b) const {
        return Mod(val * b);
    }
    Mod fpow(ll exp) const {
        Mod res(1), base(val);
        while (exp > 0) {
            if (exp & 1) res = res * base;
            base = base * base;
            exp >>= 1;
        }
        return res;
    }
    Mod inv() const {
        return fpow(p - 2);
    }
    Mod operator/(const Mod &b) const {
        return *this * b.inv();
    }
    bool operator==(const Mod &b) const {
        return val == b.val;
    }
};

struct Point {
    Mod x, y;
    Point() : x(0), y(0) {}
    Point(Mod x, Mod y) : x(x), y(y) {}
    Point operator+(const Point &b) const {
        if (x == 0 && y == 0) return b;
        if (b.x == 0 && b.y == 0) return *this;
        if (x == b.x) {
            if (y == b.y) {
                Mod s = (x * x * 3 + a) / (y * 2);
                Mod x3 = s * s - x - b.x;
                Mod y3 = s * (x - x3) - y;
                return Point(x3, y3);
            } else {
                return Point(0, 0); // point at infinity
            }
        } else {
            Mod s = (b.y - y) / (b.x - x);
            Mod x3 = s * s - x - b.x;
            Mod y3 = s * (x - x3) - y;
            return Point(x3, y3);
        }
    }
    Point operator*(ll k) const {
        Point res(0, 0), cur(*this);
        while (k > 0) {
            if (k & 1) res = res + cur;
            cur = cur + cur;
            k >>= 1;
        }
        return res;
    }
};

class s_DES {
private:
    uint16_t K;
    uint8_t K1, K2;
    const int P10[10] = { 2, 4, 1, 6, 3, 9, 0, 8, 7, 5 };
    const int P8[8] = { 5, 2, 6, 3, 7, 4, 9, 8 };
    const int mv1[10] = { 1, 2, 3, 4, 0, 6, 7, 8, 9, 5 };
    const int mv2[10] = { 2, 3, 4, 0, 1, 7, 8, 9, 5, 6 };
    void generateSubkeys() {
        uint16_t S = PERMUTE(K, P10, 10);
        S = PERMUTE(S, mv1, 10);
        K1 = (uint8_t)PERMUTE(S, P8, 8);
        S = PERMUTE(S, mv2, 10);
        K2 = (uint8_t)PERMUTE(S, P8, 8);
    }
    const int IP[8] = { 1, 5, 2, 0, 3, 7, 4, 6 };
    const int IP_INV[8] = { 3, 0, 2, 4, 6, 1, 7, 5 };
    const int S0[4][4] = { { 1, 0, 3, 2 }, { 3, 2, 1, 0 }, { 0, 2, 1, 3 }, { 3, 1, 3, 2 } };
    const int S1[4][4] = { { 0, 1, 2, 3 }, { 2, 0, 1, 3 }, { 3, 0, 1, 0 }, { 2, 1, 0, 3 } };
    const int P0[4] = { 7, 4, 5, 6 };
    const int P1[4] = { 5, 6, 7, 4 };
    const int P4[4] = { 1, 3, 2, 0 };
    uint8_t PI_T(uint8_t x, uint8_t k) {
        uint8_t p0 = PERMUTE(x, P0, 4) ^ (k & 0x0F), p1 = PERMUTE(x, P1, 4) ^ ((k >> 4) & 0x0F);
        uint8_t q;
        SET_BIT(q, 0, S0[BIN_NUM(GET_BIT(p0, 0), GET_BIT(p0, 3))][BIN_NUM(GET_BIT(p0, 1), GET_BIT(p0, 2))] >> 1);
        SET_BIT(q, 1, S0[BIN_NUM(GET_BIT(p0, 0), GET_BIT(p0, 3))][BIN_NUM(GET_BIT(p0, 1), GET_BIT(p0, 2))] & 1);
        SET_BIT(q, 2, S1[BIN_NUM(GET_BIT(p1, 0), GET_BIT(p1, 3))][BIN_NUM(GET_BIT(p1, 1), GET_BIT(p1, 2))] >> 1);
        SET_BIT(q, 3, S1[BIN_NUM(GET_BIT(p1, 0), GET_BIT(p1, 3))][BIN_NUM(GET_BIT(p1, 1), GET_BIT(p1, 2))] & 1);
        q = PERMUTE(q, P4, 4);
        return CONCAT((x >> 4) & 0x0F, (x ^ q) & 0x0F);
    }
    uint8_t fromHex(char *s) {
        uint8_t res = 0;
        for (int i = 0; i < 2; i++) {
            res <<= 4;
            if ('0' <= s[i] && s[i] <= '9') res |= s[i] - '0';
            else if ('a' <= s[i] && s[i] <= 'f') res |= s[i] - 'a' + 10;
            else assert(("Invalid hex character", false));
        }
        return res;
    }
    void toHex(uint8_t c, char *s) {
        uint8_t res;
        for (int i = 0; i < 2; i++) {
            res = c & 0xf;
            c >>= 4;
            s[1 - i] = res < 10 ? '0' + res : 'a' + res - 10;
        }
    }
    void setKey(uint16_t key) {
        K = key;
        generateSubkeys();
    }
    uint8_t encrypt(uint8_t x) {
        x = PERMUTE(x, IP, 8);
        x = PI_T(x, K1);
        x = Theta(x);
        x = PI_T(x, K2);
        x = PERMUTE(x, IP_INV, 8);
        return x;
    }
    uint8_t decrypt(uint8_t x) {
        x = PERMUTE(x, IP, 8);
        x = PI_T(x, K2);
        x = Theta(x);
        x = PI_T(x, K1);
        x = PERMUTE(x, IP_INV, 8);
        return x;
    }
public:
    void encrypt_message(char *m, const uint32_t &key, char *C) {
        setKey(key);
        int len = strlen(m);
        for (int i = 0; i < 2 * len; i += 2) {
            uint8_t c = encrypt(m[i / 2]);
            toHex(c, C + i);
        }
    }
    void decrypt_message(char *m, const uint32_t &key) {
        setKey(key);
        int len = strlen(m);
        assert(len % 2 == 0);
        for (int i = 0; i < len / 2; i++) {
            uint8_t c = fromHex(m + i * 2);
            c = decrypt(c);
            m[i] = (char) c;
        }
        m[len / 2] = '\0';
    }
};

class ECDHE {
private:
    Point G; // The generator point G
    ll priKey; // The private key
    Point pubKey; // The public key
    ll tmpPriKey; // Temporary private key
    Point tmpPubKey; // Temporary public key
    s_DES sdes; // The s-DES encryption system
    void genTempKey() {
        printf("gen\n");
        fflush(stdout);
        scanf("%lld", &tmpPriKey);
        tmpPubKey = G * tmpPriKey;
        printf("pub_e {$%lld}, {$%lld}\n", tmpPubKey.x.val, tmpPubKey.y.val);
        fflush(stdout);
    }
    void requestTempKey(ECDHE &other) {
        printf("req_e\n");
        fflush(stdout);
        scanf("%lld %lld", &other.tmpPubKey.x.val, &other.tmpPubKey.y.val);
    }
public:
    void setG(int x, int y) {
        G.x = x;
        G.y = y;
    }
    void genPermKey() {
        printf("gen\n");
        fflush(stdout);
        scanf("%lld", &priKey);
        pubKey = G * priKey;
        printf("pub_s {$%lld}, {$%lld}\n", pubKey.x.val, pubKey.y.val);
        fflush(stdout);
    }
    void requestPermKey(ECDHE &other) {
        printf("req_s\n");
        fflush(stdout);
        scanf("%lld %lld", &other.pubKey.x.val, &other.pubKey.y.val);
    }
    void receiveMsg(ECDHE &other, char *msg) {
        requestTempKey(other);
        Point K_x = other.tmpPubKey * priKey;
        uint16_t key = (K_x.x.val ^ K_x.y.val) & 0x4ff;
        printf("req_m\n");
        fflush(stdout);
        scanf("%s", msg);
        sdes.decrypt_message(msg, key);
    }
    void sendMsg(ECDHE &other, char *msg) {
        genTempKey();
        Point K_x = other.pubKey * tmpPriKey;
        uint16_t key = (K_x.x.val ^ K_x.y.val) & 0x4ff;
        sdes.encrypt_message(msg, key, cipherText);
        printf("send {$%s}\n", cipherText);
        fflush(stdout);
    }
};

void convert() {
    int len = strlen(msgRcv);
    for (int i = 0; i < len; i++) {
        if (isalpha(msgRcv[i])) {
            cnt[tolower(msgRcv[i])]++;
        }
    }
    char *p = msgSnd;
    p += sprintf(p, "{");
    for (int i = 0; i < len; i++) {
        if (isalpha(msgRcv[i]) && cnt[tolower(msgRcv[i])] > 0) {
            p += sprintf(p, "%c:%d,", tolower(msgRcv[i]), cnt[tolower(msgRcv[i])]);
            cnt[tolower(msgRcv[i])] = 0;
        }
    }
    if (p[-1] == ',') p--;
    p += sprintf(p, "}");
}

int main() {
    scanf("%lld%lld%lld%lld%lld", &a, &b, &p, &x_g, &y_g);
    ECDHE Alice, Bob;
    Alice.setG(x_g, y_g);
    Bob.setG(x_g, y_g);
    Bob.genPermKey();
    Bob.requestPermKey(Alice);
    Bob.receiveMsg(Alice, msgRcv);
    int q = atoi(msgRcv);
    Bob.sendMsg(Alice, msgRcv);
    while (q--) {
        Bob.receiveMsg(Alice, msgRcv);
        convert();
        Bob.sendMsg(Alice, msgSnd);
        fflush(stdout);
    }
    return 0;
}