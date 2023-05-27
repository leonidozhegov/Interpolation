#include <bits/stdc++.h>
using namespace std;
#define ll long long
#define ld long double
#define fi first
#define se second
#define pb push_back
#define cok cout << (ok ? "YES\n" : "NO\n");
#define dbg(x) cout << (#x) << ": " << (x) << endl;
#define dbga(x,l,r) cout << (#x) << ": "; for (int ii=l;ii<r;ii++) cout << x[ii] << " "; cout << endl;
// #define int long long
#define pi pair<int, int>
const int N = 7, C = 1e7, MAX_DEG = 4, MAX_PRODUCT = 1e5;
const ld EPS = 1e-9, EPS_CHECK = 1e-9;
const string SEP = "  (", END = ")\n";
const bool APPROXIMATION = true;
array <string, N> names;
array <int, N> max_exp, powers, current_converted, cur_exp;
array<vector<ll>, N> POINTS;
ll DIV[N][MAX_DEG + 1][MAX_DEG + 1], PW[N][MAX_DEG + 1][MAX_DEG + 1];
ld SUM[MAX_PRODUCT];
ld F_CACHE[MAX_PRODUCT];
ll pow(ll a, int b)
{
	if (b == 0) return 1;
	if (b == 1) return a;
	ll s = pow(a, b / 2);
	s *= s;
	if (b & 1) s *= a;
	return s;
}
ld approximate(ld k)
{
	int k_ = k;
	int k__ = k_ + abs(k) / k;
	if (abs(k - k_) < EPS) return k_;
	else if (abs(k - k__) < EPS) return k__;
	else
	{
		int i = 1, j = 1;
		ld ka = abs(k);
		while (i < C && j < C)
		{
			ld p = ka * j;
			if (abs(p - i) < EPS) break;
			if (p < i) j++;
			else i++;
		}
		if (i >= C || j >= C) return k;
		if (k < 0) i = -i;
		return (ld)i / j;
	}	
}
void normalize(ld k)
{
    if (!APPROXIMATION)
    {
        cout << k << SEP;
        return;
    }
	int k_ = k;
	int k__ = k_ + abs(k) / k;
	if (abs(k - k_) < EPS) cout << k_ << SEP;
	else if (abs(k - k__) < EPS) cout << k__ << SEP;
	else
	{
		int i = 1, j = 1;
		ld ka = abs(k);
		while (i < C && j < C)
		{
			ld p = ka * j;
			if (abs(p - i) < EPS) break;
			if (p < i) j++;
			else i++;
		}
		if (i >= C || j >= C)
		{
			cout << k << SEP;
			return;
		}
		if (k < 0) i = -i;
		cout << i << "/" << j << SEP;
	}
}
struct monom
{
	array<int, N> exp;
	ld k;
	int deg;
	monom(array<int, N> v, ld k_)
	{
		k = k_;
		exp = v;
		deg = 0;
		for (int i=0;i<N;i++) deg += exp[i];
	}
	void display()
	{
		normalize(k);
		if (deg == 0) { cout << "1" << END; return;}
		bool go = 0;
		for (int i=0;i<N;i++)
		{
			if (go && exp[i]) cout << " * ";
			if (exp[i]) go = 1, cout << names[i] + "^" + to_string(exp[i]);
		}
		cout << END;
	}
	ld operator()(array<int, N> v)
	{
		ll res = 1;
		for (int i=0;i<N;i++) res *= PW[i][v[i]][exp[i]];
		return k * res;
	}
	ld getRandom(array<ll, N> v)
	{
		ld res = 1;
		for (int i=0;i<N;i++) res *= pow(v[i], exp[i]);
		return k * res;
	}
};
bool operator<(monom a, monom b)
{
	if (a.deg > b.deg) return 1;
	if (a.deg < b.deg) return 0;
	if (a.exp > b.exp) return 1;
	if (a.exp < b.exp) return 0;
	return a.k > b.k;
}
struct polynom
{
	vector<monom> st;
	void add(monom m)
	{
		if (abs(m.k) < EPS) return;
		st.pb(m);
	}
	void print() { if(st.size() == 0) {cout << "Polynom is 0\n"; return;} sort(st.begin(), st.end()); for (monom &m: st) m.display();}
	ld operator()(array<ll, N> v)
	{
		ld res = 0;
		for (auto &m: st) res += m.getRandom(v);
		return res;
	}
};
ld gen(int index=0, int current_hash=0)
{
	if (index == N)
	{
		ll div = 1;
		for (int i=0;i<N;i++) div *= DIV[i][current_converted[i]][cur_exp[i]];
		return (ld)(F_CACHE[current_hash] - SUM[current_hash]) / div;
	}
	ld res = 0;
	for (int i=0;i<=cur_exp[index];i++)
	{
		current_converted[index] = i;
		res += gen(index + 1, current_hash + i * powers[index]);
	}
	return res;
}
array<int, N> convert(int h)
{
	array<int, N> res;
	for (int i=0;i<N;i++) res[i] = h / powers[i], h -= res[i] * powers[i];
	return res;
}
array<ll, N> convert_points(int h)
{
	array<ll, N> res;
	for (int i=0;i<N;i++) res[i] = POINTS[i][h / powers[i]], h %= powers[i];
	return res;
}
polynom interpolate(ld f(array<ll, N>))
{
    int max_pow = -2e9, sum = 0, h_max = 0;
    set<int> remaining_points, st;
	polynom res;
    for (int x: max_exp) max_pow = max(max_pow, x), sum += x, h_max = h_max * (x + 1) + x;

    powers[N - 1] = 1;
    for (int i=N-2;i>-1;i--) powers[i] = powers[i + 1] * (max_exp[i + 1] + 1);

    for (int i=0;i<max_exp.size();i++) for (int j=0;j<=max_exp[i];j++) POINTS[i].pb(j);
	
    for (int i=0;i<N;i++) for (int j=0;j<=max_exp[i];j++) for (int u=0;u<=max_exp[i];u++) DIV[i][j][u] = (u ? DIV[i][j][u - 1] : 1) * (u == j ? 1 : (POINTS[i][j] - POINTS[i][u]));

    for (int i=0;i<N;i++) for (int j=0;j<=max_exp[i];j++) for (int u=0;u<=max_pow;u++) PW[i][j][u] = u ? PW[i][j][u - 1] * POINTS[i][j] : 1;

    for (int i=0;i<=h_max;i++) F_CACHE[i] = f(convert_points(i)), remaining_points.insert(i);
    st.insert(h_max);
	
    while (st.size())
	{
		int v = *st.rbegin();
		st.erase(v);
		remaining_points.erase(v);
		cur_exp = convert(v);
		ld k = gen();
		if (abs(k) > EPS)
		{
			if (APPROXIMATION) k = approximate(k);
			monom mn = monom(cur_exp, k);
			res.add(mn);
			for (int i: remaining_points) SUM[i] += mn(convert(i));
		}
		for (int i=0;i<N;i++) if (cur_exp[i]) st.insert(v - powers[i]);
	}
	return res;
}
ld f(array<ll, N> v)
{
	auto [a, b, c, d, e, f, g] = v;
	ld res = 0;
	for (int i=0;i<a;i++)
		for (int j=0;j<b;j++)
			for (int u=0;u<c;u++)
				for (int x=0;x<d;x++)
					for (int y=0;y<e;y++)
						for (int z=0;z<f;z++)
							for (int k=0;k<g;k++)
								res += 13ll * i * j * u * i * i * u - 49ll * k * k * z * z * y + 90ll * c * u * k * x * x * x;
	return res;
}
void check(polynom p, ld(array<ll, N> f))
{
	mt19937 rnd(228);
	for (int i=0;i<100;i++)
	{
		int t = clock();
		array<ll, N> ex;
		for (int j=0;j<N;j++) ex[j] = rnd() % 20 + 2;
		ld F = f(ex);
		ld P = p(ex);
		if (abs(F - P) > max(EPS_CHECK, EPS_CHECK * abs(F)))
		{
			cout << "Polynom is wrong, test " << i << endl;
			cout << F << endl << P << endl;
			for (int x: ex) cout << x << " ";
			cout << endl;
			return;
		}
		cout << "Test " << i << " has been passed, time = " << (ld)(clock() - t) / CLOCKS_PER_SEC << "s" << endl;
	}
	cout << "Polynom is OK" << endl;
}
signed main()
{
    cin.tie(0); ios_base::sync_with_stdio(0);
    cout << setprecision(20) << fixed;

    names = {"a", "b", "c", "d", "e", "f", "g"};
    max_exp = {4, 2, 3, 4, 2, 3, 3};
    
    polynom P = interpolate(f);
    P.print();
    cout << "Checking polynom..." << endl;
    check(P, f);
}
