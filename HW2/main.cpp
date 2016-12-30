
#include <fstream>
#include <iostream>
#include <string>
#include <vector>
#include <map>
#include <set>
#include <vector>

using namespace std;

const int N = 5000;

int cnt = 0;
long long prime[N * N];

string getStringWithoutSpaces(const string & s) {
	string res = "";
	for (unsigned int i = 0; i < s.length(); i++) {
		char c = s[i];
		if (!isspace(c)) res += c;
	}
	return res;
}

struct Node {
	long long hash;
	int vertCnt;
	int ptrCnt;
	bool lastValue;
	vector<Node*> terms;
	string s;
	Node * l;
	Node * r;
	Node() : vertCnt(0), ptrCnt(0), l(NULL), r(NULL) {}
	Node(string s, Node * l, Node * r) : s(s), l(l), r(r) {
		vertCnt = 1;
		ptrCnt = 0;
		int lCnt = 0, rCnt = 0;
		if (l) {
			lCnt = l->vertCnt;
			vertCnt += lCnt;
			l->ptrCnt++;
		}
		if (r) {
			rCnt = r->vertCnt;
			vertCnt += rCnt;
		}
		hash = 0;
		if (l) hash += l->hash;
		for (size_t i = 0; i < s.length(); i++) {
			hash *= prime[1];
			hash += s[i];
		}
		if (r) {
			hash *= prime[rCnt];
			hash += r->hash;
			r->ptrCnt++;
		}

	}
	Node(string s, vector<Node*> &terms) : Node(s, NULL, NULL) {
		this->terms = terms;
		hash = terms[0]->hash;
		for (size_t i = 1; i < terms.size(); i++) {
			hash *= prime[terms[i]->vertCnt];
			hash += terms[i]->hash;
		}
		for (size_t i = 0; i < s.length(); i++) {
			hash *= prime[1];
			hash += s[i];
		}
	}

	~Node() {
		if (l && l->ptrCnt == 0) delete l;
		if (r && r->ptrCnt == 0) delete r;
	}
	string getAsString(bool isMain = true) {
		string result = "";
		if (!isVariable() && !isMain) {
			result += "(";
		}
		if (s != "@" && s != "?") {
			if (l) {
				result += l->getAsString(false);
			}
			result += s;
		}
		else {
			result += s;
			if (l) {
				result += l->getAsString(false);
			}
		}
		if (r) {
			result += r->getAsString(false);
		}
		if (terms.size() != 0) {
			result += "(";
			for (size_t i = 0; i < terms.size() - 1; i++) {
				result += terms[i]->getAsString() + ",";
			}
			result += terms.back()->getAsString();
			result += ")";
		}
		if (!isVariable() && !isMain) {
			result += ")";
		}
		return result;
	}

	bool isVariable() {
		if (s.length() > 0 && s[0] >= 'a' && s[0] <= 'z' && terms.size() == 0) {
			return true;
		}
		return false;
	}

	bool isFunction() {
		if (s.length() > 0 &&
			(
			(s[0] >= 'a' && s[0] <= 'z' && terms.size() != 0) ||
				s[0] == '\'' || s[0] == '*' || s[0] == '+' || s[0] == '0'
				)) {
			return true;
		}
		return false;
	}

	bool isPredicate() {
		if (s.length() > 0 && s[0] >= 'A' && s[0] <= 'Z') {
			return true;
		}
		return false;
	}
};

struct SubstituteError {
	Node *x, *y;
	string a;
	SubstituteError(Node *y, const string &a, Node *x) : x(x), y(y), a(a) {}
};

struct VariableFreeError {
	Node *x;
	string a;
	VariableFreeError(Node *x, const string &a) : x(x), a(a) {}
};

struct KvantorError {
	string type;
	string a;
	Node *x;
	KvantorError(const string &type, const string &a, Node *x) : type(type), a(a), x(x) {}
};

struct UnknownError {

};

Node *notX(Node *x) {
	return new Node("!", NULL, x);
}

Node *notNotX(Node *x) {
	return notX(notX(x));
}

#include "parser.h"

vector<Node*> axioms;

bool checkEqual(Node * a, Node * b) {
	if (!a && !b) return true;
	if (!a || !b) return false;
	if (a == b) return true;
	if (a->hash != b->hash) return false;
	else return true;
	if (a->terms.size() != b->terms.size()) return false;
	if (a->s != b->s) return false;
	for (size_t i = 0; i < a->terms.size(); i++) {
		if (!checkEqual(a->terms[i], b->terms[i])) {
			return false;
		}
	}
	if (!checkEqual(a->l, b->l)) return false;
	if (!checkEqual(a->r, b->r)) return false;
	return true;
}

// by predicate or by variable
bool fillMap(Node * formula, Node * template_, map<string, vector<Node *> > &variableMap, bool byPred = true) {
	if (!formula && !template_) return true;
	if (!formula || !template_) return false;
	const string &tempStr = template_->s;
	if (byPred && template_->isPredicate() || !byPred && template_->isVariable()) {
		variableMap[tempStr].push_back(formula);
		return true;
	}
	else {
		if (tempStr != formula->s) {
			return false;
		}
		return fillMap(formula->l, template_->l, variableMap, byPred) &&
			fillMap(formula->r, template_->r, variableMap, byPred);
	}
}

// by predicate or by variable
bool checkFormulaIsSimilarToTemplate(Node *formula, Node *template_, bool byPred = true) {
	if (!formula && !template_) return true;
	if (!formula || !template_) return false;
	if (formula == template_) return true;
	map<string, vector<Node*> > variableMap;
	if (fillMap(formula, template_, variableMap, byPred)) {
		for (auto& it : variableMap) {
			vector<Node*> &nodes = it.second;
			for (Node* node : nodes) {
				if (!checkEqual(node, *nodes.begin())) {
					return false;
				}
			}
		}
		return true;
	}
	return false;
}

// for 11, 12, 21 axioms
bool checkFormulaIsSimilarToTemplate2(Node *formula, Node *template_) {
	if (!formula && !template_) return true;
	if (!formula || !template_) return false;
	if (formula == template_) return true;
	if (template_->isVariable()) {
		return formula->isVariable();
	}
	if (template_->isPredicate()) {
		return true;
	}
	if (formula->s != template_->s) {
		return false;
	}
	return checkFormulaIsSimilarToTemplate2(formula->l, template_->l) &&
		checkFormulaIsSimilarToTemplate2(formula->r, template_->r);
}

Node *getFirstNotBound(Node *formula, Node *template_, const string &x) {
	if (!formula || !template_) return NULL;
	if (template_->s == x) {
		return formula;
	}

	if (template_->s != formula->s) {
		return NULL;
	}

	if (template_->terms.size() != formula->terms.size()) {
		return NULL;
	}

	bool isKvant = false;
	if (formula->s == "@" || formula->s == "?") {
		if (formula->l->s == x) {
			return NULL;
		}
		isKvant = true;
	}

	for (size_t i = 0; i < formula->terms.size(); i++) {
		Node *res = getFirstNotBound(formula->terms[i],
			template_->terms[i],
			x);
		if (res) return res;
	}

	if (!isKvant) {
		Node *res1 = getFirstNotBound(formula->l, template_->l, x);
		if (res1) return res1;
	}
	Node *res2 = getFirstNotBound(formula->r, template_->r, x);
	if (res2) return res2;
	return NULL;
}

bool checkIsFreeForSub(Node *v, const map<string, int> &bounded) {
	if (!v) return true;
	for (Node *term : v->terms) {
		if (!checkIsFreeForSub(term, bounded)) {
			return false;
		}
	}
	if (v->isVariable()) {
		auto it = bounded.find(v->s);
		return it == bounded.end() || it->second == 0;
	}
	return checkIsFreeForSub(v->l, bounded) && checkIsFreeForSub(v->r, bounded);
}

bool checkIsNotFree(Node *v, const string &x, map<string, int> &bounded) {
	if (!v) return true;
	if (v->s == "@" || v->s == "?") {
		bounded[v->l->s]++;
	}

	if (v->isVariable()) {
		auto it = bounded.find(v->s);
		return it == bounded.end() || it->second != 0;
	}
	bool result = checkIsNotFree(v->l, x, bounded) && checkIsNotFree(v->r, x, bounded);
	if (v->s == "@" || v->s == "?") {
		bounded[v->l->s]--;
	}
	return result;
}

bool checkIsNotFree(Node *v, const string &x) {
	map<string, int> bounded;
	return checkIsNotFree(v, x, bounded);
}

Node *substitute(Node *alpha, const string &x, Node *tetta, map<string, int> &bounded, bool &isFree) {
	if (!alpha) return NULL;

	bool isKvant = false;
	if (alpha->s == "@" || alpha->s == "?") {
		if (alpha->l->s == x) {
			return alpha;
		}
		bounded[alpha->l->s]++;
		isKvant = true;
		return new Node(alpha->s,
			alpha->l,
			substitute(alpha->r, x, tetta, bounded, isFree));
	}
	Node *result = NULL;
	if (alpha->s == x) {
		if (!checkIsFreeForSub(tetta, bounded)) {
			isFree = false;
		}
		result = tetta;
	}
	else {
		if (alpha->terms.size() == 0) {
			result = new Node(alpha->s,
				substitute(alpha->l, x, tetta, bounded, isFree),
				substitute(alpha->r, x, tetta, bounded, isFree));
		}
		else {
			vector<Node*> terms;
			for (Node *term : alpha->terms) {
				terms.push_back(substitute(term, x, tetta, bounded, isFree));
			}
			result = new Node(alpha->s, terms);
		}
	}
	if (isKvant) {
		bounded[alpha->l->s]--;
	}
	return result;
}

// alpha[x:=tetta]
Node *substitute(Node *alpha, const string &x, Node *tetta, bool &isFree) {
	map<string, int> bounded;
	Node *result = substitute(alpha, x, tetta, bounded, isFree);
	return result;
}

Node *getFormulaFromTemplate(Node *v, Node *a = NULL, Node *b = NULL, Node *c = NULL) {
	if (!v) return NULL;
	if (v->s == "A") return a;
	if (v->s == "B") return b;
	if (v->s == "C") return c;
	return new Node(v->s,
		getFormulaFromTemplate(v->l, a, b, c),
		getFormulaFromTemplate(v->r, a, b, c));
}

void init() {
	prime[0] = 1;
	prime[1] = 31;
	for (int i = 2; i < N * N; i++) {
		prime[i] = prime[i - 1] * prime[1];
	}
	axioms = vector<Node*>(30);
	axioms[1] = parseStringToFormula("A->B->A");
	axioms[2] = parseStringToFormula("(A->B)->(A->B->C)->(A->C)");
	axioms[3] = parseStringToFormula("A->B->A&B");
	axioms[4] = parseStringToFormula("A&B->A");
	axioms[5] = parseStringToFormula("A&B->B");
	axioms[6] = parseStringToFormula("A->A|B");
	axioms[7] = parseStringToFormula("B->A|B");
	axioms[8] = parseStringToFormula("(A->C)->(B->C)->(A|B->C)");
	axioms[9] = parseStringToFormula("(A->B)->(A->!B)->!A");
	axioms[10] = parseStringToFormula("!!A->A");

	axioms[11] = parseStringToFormula("@xA->A(x)");
	axioms[12] = parseStringToFormula("A(x)->?xA");

	axioms[13] = parseStringToFormula("a=b->a'=b'");
	axioms[14] = parseStringToFormula("a=b->a=c->b=c");
	axioms[15] = parseStringToFormula("a'=b'->a=b");
	axioms[16] = parseStringToFormula("!a'=0");
	axioms[17] = parseStringToFormula("a+b'=(a+b)'");
	axioms[18] = parseStringToFormula("a+0=a");
	axioms[19] = parseStringToFormula("a*0=0");
	axioms[20] = parseStringToFormula("a*b'=a*b+a");
	axioms[21] = parseStringToFormula("A(x)&@x(A->A(x))->A");
}

int checkIsAxiom(Node *formula) {
	for (int i = 1; i <= 10; i++) {
		if (checkFormulaIsSimilarToTemplate(formula, axioms[i])) {
			return i;
		}
	}
	if (checkFormulaIsSimilarToTemplate2(formula, axioms[11])) {
		Node *x = getFirstNotBound(formula->r,
			formula->l->r,
			formula->l->l->s);
		if (x) {
			bool isFree = true;
			Node *sub = substitute(formula->l->r,
				formula->l->l->s,
				x, isFree);
			if (checkEqual(sub, formula->r)) {
				if (isFree) {
					return 11;
				}
				else {
					throw SubstituteError(formula->l->r,
						formula->l->l->s,
						x);
				}
			}
		}
		else {
			if (checkEqual(formula->l->r, formula->r)) return 11;
		}
	}
	if (checkFormulaIsSimilarToTemplate2(formula, axioms[12])) {
		Node *x = getFirstNotBound(formula->l,
			formula->r->r,
			formula->r->l->s);
		if (x) {
			bool isFree = true;
			Node *sub = substitute(formula->r->r,
				formula->r->l->s,
				x, isFree);
			if (checkEqual(sub, formula->l)) {
				if (isFree) {
					return 12;
				}
				else {
					throw SubstituteError(formula->r->r,
						formula->r->l->s,
						x);
				}
			}
		}
		else {
			if (checkEqual(formula->r->r, formula->l)) return 12;
		}
	}

	for (int i = 13; i <= 20; i++) {
		if (checkEqual(formula, axioms[i])) {
			return i;
		}
	}
	if (checkFormulaIsSimilarToTemplate2(formula, axioms[21])) {
		if (checkEqual(formula->r, formula->l->r->r->l)) {
			const string &x = formula->l->r->l->s;
			bool isFree = true;
			Node *sub0 = substitute(formula->r, x, new Node("0", NULL, NULL), isFree);
			if (checkEqual(sub0, formula->l->l)) {
				Node *subx = substitute(formula->r, x, new Node("\'", new Node(x, NULL, NULL), NULL), isFree);
				if (checkEqual(subx, formula->l->r->r->r)) {
					return 21;
				}
			}
		}
	}

	return -1;
}

bool checkForallRule(Node *v, const vector<Node*> &formulas) {
	if (v->s == "->" && v->r->s == "@") {
		Node *toFind = new Node("->", v->l, v->r->r);
		for (Node *formula : formulas) {
			if (checkEqual(toFind, formula)) {
				if (checkIsNotFree(v->l, v->r->l->s)) {
					return true;
				}
				else {
					throw VariableFreeError(v->l, v->r->l->s);
				}
			}
		}
	}
	return false;
}

bool checkExistsRule(Node *v, const vector<Node*> &formulas) {
	if (v->s == "->" && v->l->s == "?") {
		Node *toFind = new Node("->", v->l->r, v->r);
		for (size_t i = 0; i < formulas.size(); i++) {
			Node *formula = formulas[i];
			if (checkEqual(toFind, formula)) {
				if (checkIsNotFree(v->r, v->l->l->s)) {
					return true;
				}
				else {
					throw VariableFreeError(v->r, v->l->l->s);
				}
			}
		}
	}
	return false;
}

bool parseTitle(const string &ss, vector<Node*> &supposes, Node *&alpha, Node *&betta) {
	const string s = getStringWithoutSpaces(ss);
	for (size_t i = 0; i < s.length() - 1; i++) {
		if (s[i] == '|' && s[i + 1] == '-') {
			int ptr = i + 2;
			betta = parseExpression(s, ptr);
			if (i == 0) return true;
			const string t = s.substr(0, i);
			ptr = 0;
			while (ptr < (int)t.length()) {
				Node *expr = parseExpression(t, ptr);
				if (ptr < (int)t.length() && t[ptr] != ',') throw "bad supposes list";
				if (ptr < (int)t.length()) {
					supposes.push_back(expr);
				}
				else {
					alpha = expr;
				}
				ptr++;
			}

			return true;
		}
	}
	return false;
}

bool checkIsSuppose(Node *formula, const vector<Node*> &supposes) {
	for (Node *suppose : supposes) {
		if (checkEqual(suppose, formula)) {
			return true;
		}
	}
	return false;
}

Node *checkIsModusPonens(Node *formula, const vector<Node*> &formulas) {
	for (Node *vf : formulas) {
		if (vf->s == "->" && checkEqual(vf->r, formula)) {
			for (Node *v : formulas) {
				if (checkEqual(v, vf->l)) {
					return v;
				}
			}
		}
	}
	return NULL;
}

bool checkVarIsFreeInFormula(const string &a, Node *v, bool isFree = true) {
	if (!v) {
		return false;
	}
	if (v->isVariable()) {
		if (v->s == a) {
			return isFree;
		}
		else {
			return false;
		}
	}
	for (Node *term : v->terms) {
		if (checkVarIsFreeInFormula(a, term, isFree)) {
			return true;
		}
	}
	if (v->s == "@" || v->s == "?") {
		return checkVarIsFreeInFormula(a, v->r, (v->l->s == a ? false : true) & isFree);
	}
	if (checkVarIsFreeInFormula(a, v->l, isFree) || checkVarIsFreeInFormula(a, v->r, isFree)) {
		return true;
	}
	return false;
}

Node *getAxiom(int number, Node *a = NULL, Node *b = NULL, Node *c = NULL) {
	return getFormulaFromTemplate(axioms[number], a, b, c);
}

void getAA(Node *a, vector<Node*> &proof) {
	proof.push_back(getAxiom(1, a, a));
	proof.push_back(getAxiom(1, a, new Node("->", a, a)));
	proof.push_back(getAxiom(2, a, new Node("->", a, a), a));
	proof.push_back(proof.back()->r);
	proof.push_back(proof.back()->r);
}

void simpleDeduction(
	const vector<Node*> &formulas,
	const vector<Node*> &supposes,
	Node *alpha,
	Node *betta,
	vector<Node*> &proof,
	int supBegin_ = 0, int supEnd_ = -1,
	int forBegin_ = 0, int forEnd_ = -1) {
	if (supEnd_ == -1) {
		supEnd_ = supposes.size();
	}
	if (forEnd_ == -1) {
		forEnd_ = formulas.size();
	}

	if (!checkEqual(formulas[forEnd_ - 1], betta)) {
		throw "Deduction fail : last formula != betta";
	}

	for (int i = forBegin_; i < forEnd_; i++) {
		Node * expr = formulas[i];
		int axiomNumber = checkIsAxiom(expr);
		int proofStart = proof.size();
		if (axiomNumber != -1 || checkIsSuppose(expr, supposes)) {
			// di
			proof.push_back(expr);
			// di -> (a -> di)
			proof.push_back(getAxiom(1, expr, alpha));
			proof.push_back(proof.back()->r);
		}
		else if (checkEqual(expr, alpha)) {
			getAA(alpha, proof);
		}
		else {
			Node *dj = checkIsModusPonens(expr, formulas);
			if (dj != NULL) {
				// (a -> dj) -> ((a -> (dj -> di))) -> (a -> di)
				proof.push_back(getAxiom(2, alpha, dj, expr));
				// ((a -> (dj -> di))) -> (a -> di)
				proof.push_back(proof.back()->r);
				// a -> di
				proof.push_back(proof.back()->r);
			}
			else {
				cout << "OOPS: " << "\n" << expr->getAsString() << "\n";
				throw "there is an error in proof";
			}
		}
	}
}


int main() {
	int counter = 1;
	Node *formula = NULL;
	ifstream cin("input.txt");
	ofstream cout("output.txt");
	try {
		init();

		vector<Node*> supposes, formulas;
		vector<Node*> proof;
		Node *alpha = NULL;
		Node *betta = NULL;
		string title;

		getline(cin, title);
		bool f = false;
		for (size_t i = 0; i < title.size() - 1; i++) {
			if (title[i] == '|' && title[i + 1] == '-') {
				f = true;
			}
		}
		bool deduction = false;
		if (f) {
			deduction = parseTitle(title, supposes, alpha, betta);
		}
		else {
			cin.seekg(0, ios::beg);
			cin.clear();
		}

		string s;

		while (getline(cin, s)) {
			cnt++;
			if (s.length() == 0) continue;
			formula = parseStringToFormula(s);
			formulas.push_back(formula);
			int axiomNumber = -1;

			axiomNumber = checkIsAxiom(formula);
			if (axiomNumber != -1) {
				if (axiomNumber == 21 && deduction && alpha != NULL) {
					if (checkVarIsFreeInFormula(formula->l->r->l->s, alpha)) {
						throw KvantorError("�������", formula->l->r->l->s, alpha);
					}
				}
				if (axiomNumber == 11 && deduction && alpha != NULL) {
					if (checkVarIsFreeInFormula(formula->l->l->s, alpha)) {
						throw KvantorError("�������", formula->l->l->s, alpha);
					}
				}
				if (axiomNumber == 12 && deduction && alpha != NULL) {
					if (checkVarIsFreeInFormula(formula->r->l->s, alpha)) {
						throw KvantorError("�������", formula->r->l->s, alpha);
					}
				}
				if (deduction && alpha != NULL) {
					proof.push_back(formula);
					proof.push_back(getAxiom(1, formula, alpha));
					proof.push_back(proof.back()->r);
				}
			}
			else if (deduction && checkIsSuppose(formula, supposes)) {
				if (alpha != NULL) {
					proof.push_back(formula);
					proof.push_back(getAxiom(1, formula, alpha));
					proof.push_back(proof.back()->r);
				}
			}
			else if (deduction && checkEqual(formula, alpha)) {
				getAA(alpha, proof);
			}
			else if (checkForallRule(formula, formulas)) {
				if (deduction && alpha != NULL) {
					if (checkVarIsFreeInFormula(formula->r->l->s, alpha)) {
						throw KvantorError("�������", formula->r->l->s, alpha);
					}
				}
				if (checkVarIsFreeInFormula(formula->r->l->s, formula->l)) {
					throw VariableFreeError(formula->l, formula->r->l->s);
				}
				if (deduction && alpha != NULL) {
					vector<Node*> tmpSupposes;
					vector<Node*> tmpFormulas;
					vector<Node*> tmpProof;

					Node *A = alpha;
					Node *B = formula->l;
					Node *C = formula->r->r;
					////////////////////////////////////////////////////
					/// A->(B->C), A&B |- C ...
					tmpSupposes.push_back(new Node("->", A, new Node("->", B, C)));

					tmpFormulas.push_back(new Node("&", A, B));
					tmpFormulas.push_back(getAxiom(4, A, B));
					tmpFormulas.push_back(A);
					tmpFormulas.push_back(getAxiom(5, A, B));
					tmpFormulas.push_back(B);
					tmpFormulas.push_back(tmpSupposes[0]);
					tmpFormulas.push_back(tmpFormulas.back()->r);
					tmpFormulas.push_back(tmpFormulas.back()->r);

					simpleDeduction(tmpFormulas, tmpSupposes, tmpFormulas[0], C, proof);
					/// ... A&B -> C
					////////////////////////////////////////////////////
					/// A&B -> @xC
					proof.push_back(new Node("->", tmpFormulas[0], formula->r));
					////////////////////////////////////////////////////
					/// A&B->@xC,A,B |- @xC ...
					tmpSupposes.clear();
					tmpFormulas.clear();
					tmpSupposes.push_back(proof.back());
					tmpSupposes.push_back(A);

					tmpFormulas.push_back(A);
					tmpFormulas.push_back(B);
					tmpFormulas.push_back(getAxiom(3, A, B));
					tmpFormulas.push_back(tmpFormulas.back()->r);
					tmpFormulas.push_back(tmpFormulas.back()->r);
					tmpFormulas.push_back(tmpSupposes[0]);
					tmpFormulas.push_back(tmpFormulas.back()->r);

					simpleDeduction(tmpFormulas, tmpSupposes, B, formula->r, tmpProof);
					/// ... A&B->@xC,A |- B->@xC ...
					tmpSupposes.pop_back();

					simpleDeduction(tmpProof, tmpSupposes, A, tmpProof.back(), proof);
					/// ... A->B->@xC
					////////////////////////////////////////////////////
				}
			}
			else if (checkExistsRule(formula, formulas)) {
				if (deduction && alpha != NULL) {
					if (checkVarIsFreeInFormula(formula->l->l->s, alpha)) {
						throw KvantorError("�������", formula->l->l->s, alpha);
					}
				}
				if (checkVarIsFreeInFormula(formula->l->l->s, formula->r)) {
					throw VariableFreeError(formula->r, formula->l->l->s);
				}
				if (deduction && alpha != NULL) {
					Node *A = alpha;
					Node *B = formula->l->r;
					Node *C = formula->r;
					vector<Node*> tmpSupposes;
					vector<Node*> tmpFormulas;
					vector<Node*> tmpProof;

					/// A->B->C |- B->A->C
					/// A->B->C, B, A |- C ...
					tmpSupposes.push_back(new Node("->", A, new Node("->", B, C)));
					tmpSupposes.push_back(B);

					tmpFormulas.push_back(A);
					tmpFormulas.push_back(B);
					tmpFormulas.push_back(tmpSupposes[0]);
					tmpFormulas.push_back(tmpFormulas.back()->r);
					tmpFormulas.push_back(tmpFormulas.back()->r);

					simpleDeduction(tmpFormulas, tmpSupposes, A, C, tmpProof);
					/// ... A->B->C, B |- A->C
					tmpSupposes.pop_back();

					simpleDeduction(tmpProof, tmpSupposes, B, new Node("->", A, C), proof);
					/// ... A->B->C |- B->(A->C)

					/// ?xB->(A->C)
					proof.push_back(new Node("->", formula->l, new Node("->", A, C)));
					////////////////////////////////////////////////////
					/// ?xB->(A->C) |- A->(?xB->C)
					/// ?xB->(A->C), A, ?xB |- C ...
					tmpSupposes.clear();
					tmpFormulas.clear();
					tmpSupposes.push_back(proof.back());
					tmpSupposes.push_back(A);

					tmpFormulas.push_back(A);
					tmpFormulas.push_back(tmpSupposes[0]->l);
					tmpFormulas.push_back(tmpSupposes[0]);
					tmpFormulas.push_back(tmpFormulas.back()->r);
					tmpFormulas.push_back(tmpFormulas.back()->r);

					simpleDeduction(tmpFormulas, tmpSupposes, tmpSupposes[0]->l, C, tmpProof);
					/// ... ?xB->(A->C), A |- ?xB->C
					tmpSupposes.pop_back();
					simpleDeduction(tmpProof, tmpSupposes, A, formula, proof);
					/// ... A->(?xB->C)
					////////////////////////////////////////////////////
				}
			}
			else {
				Node *v = checkIsModusPonens(formula, formulas);
				if (v != NULL) {
					if (deduction && alpha != NULL) {
						proof.push_back(getAxiom(2, alpha, v, formula));
						proof.push_back(proof.back()->r);
						proof.push_back(proof.back()->r);
					}
				}
				else {
					throw UnknownError();
				}
			}
			if (!deduction || !alpha) {
				proof.push_back(formula);
			}
			counter++;
		}
		for (Node *formula : proof) {
			cout << formula->getAsString() << "\n";
		}
	}
	catch (const SubstituteError &e) {
		cout << "����� ����������� ������� � ������� " << counter << ": ";
		cout << "���� " << e.x->getAsString()
			<< " �� �������� ��� ����������� � ������� " << e.y->getAsString()
			<< " ������ ���������� " << e.a << ".\n";
	}
	catch (const VariableFreeError &e) {
		cout << "����� ����������� ������� � ������� " << counter << ": ";
		cout << "���������� " << e.a << " ������ �������� � ������� " << e.x->getAsString() << ".\n";
	}
	catch (const KvantorError &e) {
		cout << "����� ����������� ������� � ������� " << counter << ": ";
		cout << "������������ " << e.type << " � ��������� �� ���������� " << e.a
			<< ", �������� �������� � ��������� " << e.x->getAsString() << ".\n";
	}
	catch (const UnknownError &e) {
		cout << "����� ����������� ������� � ������� " << counter << ".\n";
	}
	catch (const char *c) {
		cout << c << "\n";
	}

	return 0;
}