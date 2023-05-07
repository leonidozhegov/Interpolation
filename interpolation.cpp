#include <bits/stdc++.h>
using namespace std;
#define ll long long
#define ld long double
#define fi first
#define se second
#define pb push_back
#pragma GCC optimize("unroll-loops,Ofast")
#pragma GCC target("avx2,bmi,bmi2,lzcnt,popcnt,tune=native")
#define cok cout << (ok ? "YES\n" : "NO\n");
#define dbg(x) cout << (#x) << ": " << (x) << endl;
#define dbga(x,l,r) cout << (#x) << ": "; for (int ii=l;ii<r;ii++) cout << x[ii] << " "; cout << endl;
// #define int long long
#define pi pair<int, int>
const int N = 7, C = 100000, M = 200;
const ld EPS = 1e-9, EPS_CHECK = 1e-9;
const string SEP = "  (", END = ")\n";
array <string, N> names;
array <int, N> max_exp;
array<vector<int>, N> POINTS;
ll DIV[N][M][M];
ll PW[N][M][M];
ll pow(ll a, int b)
{
	if (b == 0) return 1;
	if (b == 1) return a;
	ll s = pow(a, b / 2);
	s *= s;
	if (b & 1) s *= a;
	return s;
}
void normalize(ld k)
{
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
	ld getRandom(array<int, N> v)
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
bool operator==(monom a, monom b) {return a.exp == b.exp && abs(a.k - b.k) < EPS;}
struct polynom
{
	vector<monom> st;
	void add(monom m)
	{
		if (abs(m.k) < EPS) return;
		st.pb(m);
	}
	void print() { if(st.size() == 0) {cout << "Polynom is a constant 0\n"; return;} sort(st.begin(), st.end()); for (monom &m: st) m.display();}
	ld operator()(array<int, N> v)
	{
		ld res = 0;
		for (auto &m: st) res += m(v);
		return res;
	}
	ld getRandom(array<int, N> v)
	{
		ld res = 0;
		for (auto &m: st) res += m.getRandom(v);
		return res;
	}
};
bool operator==(polynom a, polynom b)
{
	if (a.st.size() != b.st.size()) return 0;
	sort(a.st.begin(), a.st.end());
	sort(b.st.begin(), b.st.end());
	return a.st == b.st;
}
array<int, N> v;
array<int, N> v_index;
int tf, tp;
ld gen(ld f(array<int, N>), array<int, N> &exp, polynom &p, int index=0)
{
	if (index == N)
	{
		ld val = f(v) - p(v_index);
		ll div = 1;
		for (int i=0;i<N;i++) div *= DIV[i][v_index[i]][exp[i]];
		return val / div;
	}
	ld res = 0;
	for (int i=0;i<=exp[index];i++)
	{
		v_index[index] = i;
		v[index] = POINTS[index][i];
		res += gen(f, exp, p, index + 1);
	}
	return res;
}
polynom interpolate(ld f(array<int, N>))
{
    int max_pow = -2e9;
    for (int x: max_exp) max_pow = max(max_pow, x);
    for (int i=0;i<max_exp.size();i++) for (int j=0;j<=max_exp[i];j++) POINTS[i].pb(j);
	for (int i=0;i<N;i++) for (int j=0;j<=max_exp[i];j++) for (int u=0;u<=max_exp[i];u++) DIV[i][j][u] = (u ? DIV[i][j][u - 1] : 1) * (u == j ? 1 : (POINTS[i][j] - POINTS[i][u]));
    for (int i=0;i<N;i++) for (int j=0;j<=max_exp[i];j++) for (int u=0;u<=max_pow;u++) PW[i][j][u] = u ? PW[i][j][u - 1] * POINTS[i][j] : 1;
	polynom res;
	int sum = 0;
	for (int x: max_exp) sum += x;
	set<pair<int, array<int, N>>> st;
	st.insert({sum, max_exp});
	while (st.size())
	{
		auto [deg, v] = *st.rbegin();
		st.erase({deg, v});
		deg--;
		ld K = gen(f, v, res);
		if (abs(K) > EPS) res.add(monom(v, K));
		for (int i=0;i<N;i++)
		{
			if (v[i])
			{
				v[i]--;
				st.insert({deg, v});
				v[i]++;
			}
		}
	}
	return res;
}
/*ld f(array<int, N> v)
{
	auto [a, b, c, d, e, f, g, h, i, j] = v;
	ld res = 0;
	for (int x1=0;x1<a;x1++)
		for (int x2=0;x2<b;x2++)
			for (int x3=0;x3<c;x3++)
				for (int x4=0;x4<d;x4++)
					for (int x5=0;x5<e;x5++)
						for (int x6=0;x6<f;x6++)
							for (int x7=0;x7<g;x7++)
								for (int x8=0;x8<h;x8++)
									for (int x9=0;x9<i;x9++)
										for (int x10=0;x10<j;x10++)
											res += (ld)312 * x1 * x1 * x6 * x7 * x9 + (ld)-15 * x1 * x8 * x4 * x4 * x5 * x10 * x10 + (ld)228 * x4 * x3 * x3 * x6 * x9 + (ld)-1029 * x5 * x9 * x4 * x4 * x2 + (ld)392 * x2 * x3 * x7 * x7 * x9 * x9 * x10 * x10;
	return res;
}*/
ld f(array<int, N> v)
{
	auto[ a, b, c, d, e, f, g] = v;
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
void check(polynom p, ld(array<int, N> f))
{
	mt19937 rnd(228);
	for (int i=0;i<100;i++)
	{
		int t = clock();
		array<int, N> ex;
		for (int j=0;j<N;j++) ex[j] = rnd() % 20 + 2;
		ld F = f(ex);
		ld P = p.getRandom(ex);
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
    cout << endl;
    cout << "Checking polynom..." << endl;
    check(P, f);
}