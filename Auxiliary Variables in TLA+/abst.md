# 1 Introduction

implementations が Higher-level specificationを満たすことは、以下を要求している
- そのspecificationにおいてHigher-level concepts がLower-level のimplementationされたデータ構造でいかにして表現されているかを、説明すること

このアプローチの歴史：

- Sequential Systemの領域でHoareの命名: `abstraction function`
- Concurrent Systemsに一般化した場合のAbadiとLamportの命名: `refinement mapping`
  - refinement mappingを構成するときは、補助変数(`auxiliary variable`)をimplementationに追加する必要があるかも。
    - 補助変数(`auxiliary variable`)は実際の変数の振る舞いに影響を与えず、かつ、実装(implement)する必要はないもの

本論文の目的：
- 補助変数をTLA+ Specificationsにどうやって追加するかを学ぶ

筆者の期待：
- 如何にしてSpecificationsに補助変数を追加するかの方法を学ぶにあたって、既存のspecificationsを慎重に学んでいる必要がある

三種類の補助変数(`auxiliary variables`):
1. history (歴史)
2. prophecy (預言)
3. stuttering (どもり)

- `History variables`: システムの過去の振る舞いに関する情報を保存するもの(別名、`ghost variables`)
- `Prophecy variables`: システムの将来の振る舞いを予言するもの。linearizabilityに関する研究で出てきたoriginalのものではなく、新しく使いやすいものを本書では扱う。
- `Stuttering variables`: 実際の変数を何も変更しない"stuttering stepsを追加するもの

Auxiliary VariablesはLivenessの条件には影響を与えないので、Livess については少しだけ言及する。

# 2 Refinement Mappings

想定している事柄として、定数を導入する。

シンプルで使い道のないようなものでまずは考える。
The server responds to each input value `i` with one of the following outputs:

- `Hi` if i is the largest number input so far, 
- `Lo` if it's the smallest number input so far, 
- `Both` if it's both, and
- `None` if it's neither.

## 2.1 Specication `MinMax1`

まずは変数を決める。

The module named `MinMax1` describes the interaction of the user and the server with two variables:

1. variable `x` to hold an input or a response,
2. a variable `turn` that indicates whether it's the user's turn to input a value or the server's turn to respond.

The specication also uses a variable y to hold the set of values input so far.

初期値を決める。

Nextに入るアクションを決める。InputNumとRespondの2つがある。

InputNumはすごく単純。ただし、enabledになるのはturn = "input"の場合のみ。

Respondについては単純にするために`setMax`と`setMin`を導入する。
enabledになるのはturn = "output"の場合のみ。

これでSpecを定義できる。varsには使う変数のタプルを入れる。

## 2.2 The Hiding Operator \EE

用語：

- a `behavior` is a sequence of `states`
- a `state` is an assignment of values to all possible variables
  - 全てのありうる変数への値の割り当てが `state` 

2つの変数：

- the externally visible or observable values of the specication
- internal variable.

Internal Variableは`\EE`で書くことができる。

- `F`: temporal formula
- `v`: variable

Defiition of `\EE v: F`:

厳密な定義は複雑なので、単純に説明する(ひとつの`state`や`value`で真になるのではなく、`behavior`において真になる。)
- behavior `\sigma` satisfies `\EE v: F` 
- iff. there eists a behavior `\tau` s.t.
  - `\tau` satisfies `F`
  - `\tau` is identical to `\sigma` except for the values its states assign to `v`

> The operator `\EE` is much like the ordinary existential quantier `\E` 
except that `\EE v : F` asserts the existence 
not of a single value for `v`  that makes `F` true 
but rather of a sequence of values, one for each state in the behavior, that makes `F` true on the behavior.

MinMax1で`\EE y: Spec`を導入しない理由：

- `y` が `Spec`の定義の中に表れていて、式がillegalになるから

e.g., `{v \in exp : v^2 > 42}`という表現は、`v`がすでに宣言もしくは定義されているModuleの中では許容しない。

hidden variable `v`を含む`Spec`の式を書く方法(ways to write the formula `Spec` with `v` hidden in TLA+.):

(1) MinMax1を生成する別のモジュールを書く

別のモジュールを書くのは、TLA+ tools は `\EE` を含むspecificationをチェックできないから。(there's little reason to do it since the TLA+ tools cannot check specications written with `\EE`)
TLAPSは場合によってはできる。

別のモジュールを書く方法の詳細：

- `\EE y : Spec`を`\EE y : [|Spec|]`の省略形とみなす(we take the formula `\EE y : Spec` to be an abbreviation for the formula `\EE y : [|Spec|]` , )
  - `[|Spec|]`は`Spec`から全ての定義を拡張して得られたもの(where `[|Spec|]` is the formula obtained from `Spec` by expanding all definitions. )
  - `[|Spec|]`はTLA+の原始的なもののみを含んでいるとする(Formula `[|Spec|]` contains only: TLA+ primitives;)
- `y` がすでに意味を与えられているなら、新たなsymbolに置き換える必要がある。(If used in a context in which `y` already has a meaning,)
  - we interpret `\EE y : Spec` to be the formula obtained from `\EE y : [|Spec|]` by replacing `y` everywhere with a new symbol.

expression内の定義の全てを拡張することは難しい

難しさの原因:
- the bound identier in the defition of formula is not the same as the one declared in the constant declaration.

expression内の定義の全てを拡張するの意味を定義するもっとも簡単な方法：
- replace variable new symbol `v_743` where `v_743` is an identier that cannot be used anywhere else

再帰的な定義は、定義の拡張においては問題ではない。
(Recursive denitions are not a problem for complete expansion of definitions)

なぜなら再帰的定義の左辺と右辺に表れるbound indentifierは同じsymbolではないから。(実際のところは `CHOOSE` 使ってるから)

## 2.3 Specication MinMax2

> The specication of our system in module `MinMax1` uses the variable `y` 
to remember the set of all values that the user has input.

> Module `MinMax2` species the same user/server interaction that 
remembers only the smallest and largest values input so far, 
using the variables min and max.

Module `MinMax1` では `y` を使って、ユーザーが入力した全ての値の集合を記憶していた。
Module `MinMax2` では、同じユーザー/サーヴァーの相互作用は、入力された最小と最大の値のみを保存する。保存については変数 `min` と `max` を使う。

The philosophically correct specification, which hides the internal variables min and max, is `\EE min; max : Spec` .

#### 疑問点

なんで今度は`\EE`が導入できるの？
-> そもそも導入できると言っているのか？
-> あとで`MinMax1`の中で置き換えているから、確かにPhilosophically correct specificationであるのかもしれない。

MinMax1で`\EE y: Spec`と書けなかった理由は、
`y` が `Spec`の定義の中に表れていて、式がillegalになるからということだった。

MinMax2での`min`と`max`はどうか？

変数としては表れている。

yの初期値は`{}`と空集合で定義されている。(それはMinMax1の中で)
minとmaxの初期値はInfinityとして独自に定義している。

`setMin(y')`などがなくなった。
結局`x = min'`などで見ると、`y'`を使っているのと代わりないように思える。

`y`は集合で、要素はintであった。
`min`や`max`はintもしくはInfinity, MinusInfinity。

-> やっぱり、どこで本質的に違いがうまれているのかがわからないから、次節の2.4まで読まないとわからないのかもしれない。

## 2.4 The Relation Between the Two Specications

`Spec2` indicates the `Spec` of `MinMax2`.

(2.5) `\EE y: Spec \<equiv> (\EE min, max : Spec2)`

- (2.6) `(\EE y : Spec1) => (\EE min, max : Spec2)`
- (2.7) `(\EE min, max : Spec2) => (\EE y : Spec1)`

(2.6):
asserts of a behavior `\sigma` that
  if there exists some way of assigning values to `y` in the states of `\sigma` to make it satisfy `Spec1`, 
  then `\sigma` satises `\EE min, max : Spec2`

changing the values of y in the states of \sigma doesn't affect whether it satisfies.

it suffices to show that any behavior `\sigma` that satises `Spec1` also satises `\EE min, max : Spec2`

i.e., 
- (2.8) `Spec1 => (\EE min,max : Spec2)`

to find explicit expressions `min` and `max` such that, if in each state of a behavior
we assign to the variables `min` and `max` the values of `\bar{min}` and `\bar{max}` in that
state, then the resulting behavior satises `Spec2`.

instantiate:

`M == INSTANCE MinMax2 with min <- BAR{min}, max <- BAR{max}`

the instance statement theorefore allow us to write the theorem:

`THEOREM Spec => M !Spec`

- We can write a TLA+ proof of this theorem and check it with the TLAPS theorem prover.
- We can also check this theorem by crateing a model.

Before do the above, we have to determine what the expressions `\bar{min}` and `\bar{max}` are in the instance statement.

## 2.5 Renement In General

Suppose that:

- x: the set of externally visible variables
- y, z: the sets of internal variables

Spec with internal variables hidden:
- `\EE y: Spec1`
- `\EE z: Spec2`

To verify `\EE y: Spec1` implements `\EE z: Spec2`,

First, show that 
- for each behavior satisfying `Spec1`, 
- there is some way to assign values of the variables `z` in each state 
  - so that the resulting behavior satises `Spec2`.

How do this?:

- by explicitly specifying those values of `z` in terms of the values of `x` and `y`.
  - for each `z_i`, define an expression `\bar{z_i}` in terms of `x` and `y`
  - show that `Spec1` implements `\bar{[[Spec2]]}`
    - by expanding all definitions in `Spec2` and substituting `z_1 <- \bar{z_1}`, ..., `z_p <- \bar{z_p}`

What they are called?:

- This substitution is called `refinement mapping`
- "Spec1 implements Spec2 under the refinement mapping"

Next, add the new instance statement in the Module of Spec1, s.t.,:

`Id == INSTANCE Mod2 WITH z1 <- newZ1, ... zp <- newZp`

.

And finally, add the theorem, s.t., :

`THEOREM Spec => Id!SPec2`

.

> it is sometimes the case that \EE y : Spec1 implements \EE z : Spec2
but there does not exist a renement mapping under which Spec1 implements
Spec2.

まじ？

> it is almost always possible to construct the necessary
renement mapping by adding auxiliary variables to Spec1

補助変数が必要になるわけだ。

`x`と`y`で代入する変数が定義できないなら、新たな補助変数`a`を導入するまでよ。

1. add a new auxiliary variables to `Spec1` s.t. `\EE a : Speca1^a` is equivalent to `Spec1`. 
2. Showing that `\EE y, a : Speca1^a` implements `\EE z : Spec2` 
3. this means that shows that `\EE y : Spec1` implements `\EE z : Spec2`

導入する三つ補助変数(再掲)

- history variables
- prophecy variables
- stuttering variables

# 3 History Variables

## 3.1 Equivalence of MinMax1 and MinMax2

> We found a renement mapping under which Spec1 implements Spec2.
> To prove the converse implication, find a renement mapping under which Spec2 implements Spec1.

> in a behavior of Spec2, the variables min and max record only
the smallest and largest input values. There is no way to reconstruct the set
of all values input from the variables of MinMax2
> there is no refinement mapping under which Spec2 implements Spec1.
> To solve this problem, we write another spec Spec_2^h that is the same as Spec2
> More precisely, if we hide h in Spec_2^h, then we get a specication that's equivalent to Spec2. 
Expressed mathematically, this means \EE h : Spec^h_2 is equivalent to Spec2.

> In particular, the value of h records information about previous values of the variable x , but
does not affect the current or future values of x or any of the other variables turn, min, and max of Spec2.

see MinMax2H.tla

## 3.2 Disjunctive Representation

We add a history variable `h` to a specication by 
- conjoining `h` = `expInit` to its initial predicate and
  - can contain the spec's variables
- (`h' = expA`) to each subaction `A` of its next-state action,
  - can contain the spec's variables

上記を適切にするためには、`subaction`が何かを明確に述べる必要がある。

NextはNext自身のsubactionと考えられ、また等しく、それはTLAPSで証明できる。

```
THEOREM NextH = /\ InputNum \/ Respond
                /\ \/ (turn = "input") /\ (h' = h)
                   \/ (turn = "output") /\ (h' = h \cup {x})
```

subactionの定義のために、`disjunctive representation`(選言表現)を導入する

Nのdisjunctive representationとは、選言(`disjunctive`, `\/`)と`\E k \in K`のみを使いsubactions A1, ..., Anで Nを書くことである。

```
B \/ C \/ D \/ (\E i \in S, j \in T:
                  (\E q \in U: E) \/ (\E r \in W: F)
                )
```

数あるDisjunctive Representation の中の1つとして、
`B`, `C \/ D`, `\E q \in U : E `, そして `F` がsubactionsだとする。

dijunction prepresentationのそれぞれのsubactionは`context`を持っている。
- contextは`<k; K>`で表現する。`k`はidentifiersのn組、`K`は表現のn組とする。
- contextの中のidentifiersの組は、Aが属するscopeの束縛している量化子のidentifiersになる。

- `B` : `<>`
- `C \/ D` : `<>`
- `\E q \in U : E ` : `<i, j; S, T>`
- `F` : `<i, j, r; S, T, W>`

If `<k;K>` is the empty context `<;>`, we let `\E <k;K> : F` and `\A <k;K> : F` equal `F`.
(Since unbounded quantication seldom occurs in specications, we will not discuss this further.)

#### 疑問

結局subactionはどう定義されたのか？

Disjunctive Representation で区切られた一つのformulaのこと？

### Theorem 1 (History Variable)

Let `Spec` equal `Init /\ [][Next]vars` and 
let `Spec^h` equal `Init^h /\ [][Next^h]vars^h`, where:

- `Init^h` equals `Init /\ (h = exp_{Init})`, for some expression expInit that may
contain the specication's (unprimed) variables.
- `Next^h` is obtained from `Next` by replacing each subaction `A` of a disjunctive
representation of `Next` with `A /\ (h' = exp_A)` , for some expression `exp_A`
that may contain primed and unprimed specication variables, identiers
in the context of `A`, and constant parameters.
- `vars^h` equals `<vars; h>`

Then `Spec` is equivalent to `\EE h : Spec^h` .

### History Variableとは何か

上記の定理の仮定に入っている。

仮定は非常に統語論的なものである: 
- `Init^h`, `Next^h`, `vars^h`の定義における条件と、
- `exp_{Init}`, `exp_A`に表れる変数とidentifirersとに関する条件

変数とidentifiersが表現`exp`の中にあらわれるというのは、そのexpの表現に表れるものの全ての定義の拡張のことである

## 3.3 Equivalence of Next-State Actions

### 補助変数を追加する時にやっているSpecの書き換えについて

When adding an auxiliary variable, 
it is often useful to rewrite a specication `Spec`
,that is, 
- to replace `Spec` with a different but equivalent formula.
- to rewrite the next-state action `Next`, 
  - which is done by rewriting one or more of the subactions in a disjunctive representation of `Next`.

A and B are equivalent formulas
 -> easy to replace, but it is too stringent a requirement.

AとBが等しいという条件は厳しすぎる要求であり、
型に関する条件を緩和すると大凡できるから、
以下のような `Inv` を導入することで、サブアクションの等しさを示す。

### Theorem 2 (Subaction Equivalence) 

仮定:

- Let `A` be a subaction with context `<k;K>` in a disjunctive representation of the next-state action of a specication `Spec` with tuple `vars` of variables, 
- let `Inv` be an invariant of `Spec`, and 
- let `B` be an action satisfying:

  (3.2) `Inv => \A <k;K> : A \equiv B`

結論：

Then `Spec` is equivalent to the specication 
  obtained by replacing `A` with `B` 
  in the next-state action's disjunctive representation.

補足：

3.2はaction formulaで、TLAPSで証明することができる。TLCではチェックできない。

また、`Inv`が単純な型のインバリアントだと、証明も難しくはない。

### TLCでの等しさの証明について

両方のspecificationがお互いを導出することを確認することで、TLCで等しさを直接確認することができる。
片方のSpecが他方のを含意することを示すためには、
`Spec` をbehavioral specificationとして、 `SpecB` をチェックする性質として、TLCを走らせればよい。

## 3.4 Discussion of History Variables

History Variablesについての議論

### 示すこと(これまでの話)

Specification `S` がある性質`P`を満たす、つまり`S` は `P` を含意することを示したい。
TLCが確認できる正しさの一般的な形式としては、一方が他方を含意することである。

また、Specification `S` が高階、より抽象的なSpecification `T`を含意することを示したい。

高階のSpecを含意することを示す方法は、
Refinement Mappingを見つけることである。
どのようなMappingかというと、Sのvariablesの値からTのvariablesの値への関数である。

しかし、Tがそのその状態において、Sによって忘れられた情報を保持している場合は、Refinement Mappingを見つけることができない。

どうやって、SがTを含意することを示すか。

1. `S`に history variable `h`を加え、`S^h`を手に入れる
2. `S^h` が `T` を含意するようなRefinement Mappingを見つける
3. `\EE h : S^h` は `S` に等しいから、`S`は`T`を含意すると言える。

### History Variable に関する反対意見

Spec `T` が実装 `S` において保存されてはならない過去の情報を保存しているならば、
`T` は良い高レベルのspecificationではない、という意見について

でも、この手の過去に関する情報は、高レベルのspecificationを、単純にしうる場合がある。

Refinement Mappingを明示的に構成していない場合においても、
Specification が満たす事項を示したいような性質について述べるために、
Specification SにHistory Variableを追加することがある。
(高レベルのものについては実装しないから)

e.g., あるactionが起きたことを記録するHistory Variableを追加しておけば、
Sがある種のactionは他のよりも先に起きたことを要求しているという性質をinvariantとして表現することができる。

## 3.5 Liveness

"every input should produce an output"といった、可能になったら動けという要求はLivenessと呼ばれ、
それをspecificationsに導入するのは、式`Spec`にWeak Fairness`WF_vars (Respond)`を付け加えることで達成される。

追加した`LSpec`の等しさの証明についてはMinMax1からMinMax2の方は、前と同様に、簡単にできるが、MinMax2からMinMax1の証明については、history variableを追加する必要がある。

MinMax2Hに`HLSpec == SpecH /\ WF_vars (Respond)`を追加する。

`LSpec` と `\EE h : HLSpec`の等しさの証明は、
`Spec` と `\EE h : SpecH`の等しさからくる。

0. `Spec` は `\EE h : SpecH`に等しいから、
1. `Spec /\ WF_vars (Respond)` は `(\EE h : SpecH) /\ WF_vars (Respond)` に等しい
2. `\EE h : SpecH) /\ WF_vars (Respond)` は `\EE h : (SpecH /\ WF_vars (Respond))`に等しい。なぜなら、`WF_vars (Respond)`に`h`は表れていないから。
3. `LSpec`と`HLSpec`の定義、1と2より、同値性が示せた。

これによてわかることは、Safety Partにhistory variableを付け加えても、Liveness条件は同じであること。

`WF_vars (Respond)`は少し不思議に思えるかもしれない。
なぜなら、`Respond`は`SpecH`のsubactionではないから。

しかし、このhistory variableの追加によって得られたSpecは不思議ではない。
(i)`Respond`は`RespondH`が可能になった時、かつその時に限り、
(ii)`NextH`stepが`Respond`stepになるのは、`RespondH`stepの時かつその時であるから、
よって、
`HLSpec`は`InitH /\ [][NextH]_varsH /\ WF_vars (Respond)`という形になる。

`HLSpec`のこの一般的ではない性質は、TLCのModel checkerにも、specificationに関する推論能力にも悪影響を及ぼさない。
history variable `h`を含むRefinement Mappingについても前と同様に作れる。

# 4 Prophecy Variables

the fundamental task of verification is
  to show that the specification Spec1 of an implementation satisfies a specication Spec2 of 
    what the implementation is supposed to do

It is needed to find a refinement mapping to show that Spec1 implements Spec2

- history variable: remembers the past
  - when Spec2 remembers previous events longer than it has to.
- prohecy variable: predicts the future
  - when Spec2 makes decisions before it has to.

## 4.1 One-Prediction Prophecy Variables

テーマ: how to add a simple prophecy variable that makes a single prediction at a time.

以下のような、ある表現`Pred_A(i)`と定数集合`\Pi`に対して、subaction Aを含むnext-state関係の選言的な表現(disjunctive representation)があると仮定する。
(4.1) `A => ( \E i \in \Pi : Pred_A(i) )`

この式は以下の式に等しい：
(4.2) `A \equiv A /\ (\E i \in \Pi : Pred_A(i))`
。これは、任意のStep `A` は、`\Pi` に属するある`i`に対して、`A /\ Pred_A(i)` であることを意味する。

one-prediction prophecy variable `p`を導入する。
  この値は`i`であり、次の `A` stepが存在する場合に、上記の`A`stepのものである。
    この`i`は一意ではない。

`p`には次のようにして意味を与える、
- subaction `A`をsubaction `A^p`で置き換える。
- `A^p`は以下のようにして定義される。
  - (4.3)`A^p == A /\ Pred_A(p) /\ Setp`
  - `Setp` は`p'`の値を決めるところのものである

propehncy variable `p` を追加することが他の変数のすべての振る舞い(元のSpecがやる)を許可するのを、保証するために、
`p` が常に `\Pi` の任意の値を取りうることを保証しなければならない
-> どうやって行うか。
1. `p` の初期化で、`\Pi`の任意の要素を取らせ
2. `p` の変更では、`\Pi`の任意の要素への変更のみによってなさせる

だから、初期化Initは `Init /\ (p \in \Pi)`にし、`Setp` は `p' \in \Pi`に等しくさせるようにし、そして
(4.4)`A^p == A /\ Pred_A(p) /\ (p' \in \Pi)`となる。

`p` によっては予言されないような効果を持っているnext-state relationの別のsubactionについては、
`A^p` が変更させないようにする、つまり：
(4.5)`A^p == A /\ p' = p`
。

例：以下のような単純なシステムを考える
- 整数`i`の送信を、変数`x`を`i`にすることで表現し
- 値を受け取ったことを、変数`x`を非整数にすることで表現する

SendInt2というSpecificationでは、受取を、内部の変数`z`に次に送信する値を割り当てることで表現してみる。

内部変数を使わずにもっとシンプルに書く方法もある。SendInt1がそれ。

SendInt1のSpec、Spec1が`\EE z: Spec2`と等しいことを示したい。以下の2つを示す必要がある宇。
- `\EE z: Spec2 => Spec1`
  - `Spec2 => Spec1`は自明で、簡単にTLCのモデル検査で、Intに対して有限の部分集合をモデルにやればよい。
- `Spec1 => \EE z: Spec2`
  - `\bar{z}`に入れることができるのは、`x`を含むものだけのようなRefinement Mappingは、明らかに、ない。
    - `x`が`NotInt`に等しい場合、`z`は任意の整数と等しくなる。
    - だから、`x`の値からの関数の値を表現する方法がない。

SendInt2の`z`は、実際に送信する前に、送信される値を予言するよう使われている。
Refinement Mappingに`\bar{z}`の値を定義できるように、予言するprophecy variable `p`を付け加えよう。

予言なんだから、送る前に値を予言しないといけないから、以下の形式になるはず
- `A^p == A /\ Pred_A(p) /\ (p' \in \Pi)`

このAにあたるのが`Send`。

`Pred_{Send}(p)`が`x' = p`と等しければ、`p`が正しく予言したことになる。
だから
- `PredSend(i) == x' = i` と定義する。
  - これのSpecでの定義は、`p`の宣言の前であり、`p`を使わずに定義されていることを保証する。

これによって、サブアクションに対する条件は以下の通りに定義される:
`Send => ( \E i \in \Pi : PredSend(i) )`
。

これにより、アクションに対する定義は次のようになる。
`SendP == Send /\ PredSend(i) /\ (p' \in Pi)`

Refinment Mappingとしては、つまり、`x`が`NotInt`に等しい場合、`z`は任意の整数と等しくなる、という条件を満たす必要がある。

補足：
- SendInt2が送信する前であったとしても、次に送信される値を予言する
  - いつ受信されるかよりもいつ送信されるか
- Rcvアクションが実行されるまで、どうやって予言を延期するのかについては後で議論するとのこと。

Theoremで示したいことは、SpecPが、Refinement Mappingの下で、SendInt2のSpecを実装していること。
これはTLCで時相プロパティ`SI2!Spec`をチェックしつつ、時相Specification `SpecP`を満たすモデルを作ることで確認できる。

## 4.2 One-Prediction Prophecy Variables in General

a one-prediction prophecy variableの説明を2つの方法で一般化する

第一の一般化: 
a prophecy variableに、1つ以上のアクションについて予言することを許す
  (4.3)`A^p == A /\ Pred_A(p) /\ Setp`の形式の`A^p`によって、1つ以上のdisjunctive representationのsbuaction Aを置き換えることによって
こうすると、各subactionについて、それぞれのstepについて次のstepで起きることを予言できるようになる。

もうちょいエレガントな表現をする、
- `Setp`を`A`に依存させて、
- dijunctive representation の各action `A`を、以下で定義される、`A^p`で置き換えることによって
  - (4.6) `A^p == A /\ Pred_A(p) /\ Setp_A`
    - `A` はなんの予言も作られていないもの
    - `Pred_A(p)` は`TRUE`の表現
    - (4.4)と(4.5)は`Setp_A`を以下のいずれかで定義することによって、これに置き換えられる
      - (4.7)
        - (a) `Setp_A == p' = p` (`Pred_A(p)` が`TRUE`の表現の場合(つまり、`p`は`A`についての予言ではない場合))
        - (b) `Setp_A == p' \in \Pi` 

これが一般的であるのは、
  それ`p`によって作られた予言を使っていないactionに、新たな予言を作ることを、許しているから。

第二の一般化:
  非-空なcontextを持っているdisjunctive representationのsubactionを扱う必要がる。

context `<<k; K>>`を持っているsubaction `A`に対して、条件(4.1) `A => ( \E i \in \Pi : Pred_A(i) )`はidentifiers `k`をもっている。
この条件は、`K`の中の対応する集合に含まれるそれぞれのidentifiersのvalueに対して、成り立つ。

だから、(4.1) `A => ( \E i \in \Pi : Pred_A(i) )`を一般化すると、

(4.8) `\A <<k; K>>:A => (\E i \in \Pi : Pred_A(i))`

になる。

(リマインド: contextは`<k; K>`で表現する。`k`はidentifiersのn組、`K`は表現のn組とする。)

(4.8) は、すべてのstateのpairにつちえ成り立つ必要はなく、元の`Spec`を満たすようなbehaviorの中に表れるsatesのpairについてだけなりたてばよい。だから、(4.1)は次のように一般化される。

(4.9) `Spec => [] [\A <k;K> : A => (\E i \in \Pi : Pred_A(i))]_vars`

TLCはこれをチェックすることが可能。

## 4.3 Prophecy Array Variables

### `Undo`操作のあるシステムについて

Module `SendInt`とは異なり、非特定のconstantな集合 Data を用意して、そこで考える。

Module `SendSet` では、`y`に新たなデータ要素を追加していく。
- `y`は内部変数で、
- `x`は外から見れる変数と考える。

システムによくあるのが`undo`オペレーション。
  `y`から要素を消すようなもの

Module `SendSetUndo`では、`Undo(S)`というactionを用意、また、next actionとして Module `SendSet`のNext もしくは`Undo(S)`をとる。
  `Undo(S)` は、`y`の非-空な部分集合Sを選んで、それを消す操作

`SendSet`の`Spec` と `SendSetUndo`の`SpecU` とは変数 `x` については振る舞いは一緒。
だから、`\EE y: Spec` と `\EE y: SpecU` とは等しい。

`Spec` が `SpecU`を含意することを示すのは簡単。
  なぜなら、`Next`で許されているようなactionは`NextU`で許されているため、
  `\overline{y}`が`y`と等しいように定義したRefinement Mappingがあるから。

`SpecU` が `Spec`を含意するようなRefinement Mappingを構成するために、
  `\overline{y}`を以下のように定義しなければならない
    - それはdata value `d`を含む、iff. 、値が`Send`Stepによって送信された場合
      - `Undo` Stepによって、値が忘れられたときではなくて

これは予言を含む、
  `d`が`y`に追加されたとき、それがのちに送信されるか、もしくは"undone"されるか。

### prophercy array variable の追加とそのSpecの定義

prophercy array variable `p`を`SpecU`に追加、
  `p`は予言を作る
    `d`が`y`に付け加えられたときに、`p[d]`が"send"か"undo"いずれに設定されるかの

だから、可能な予言の集合`Pi`は以下のように定義される
- `Pi == {"send", "undo"}`
。

これにより、`p \in [y -> Pi]`は、`p`を付け加えることによって得られるspec `SpecUP`のinvariantとなる。

変数`p`は`y`の任意の`d`に対して予言`p[d]`を作るので、`p`は予言の配列を作っている。
  (この配列は「ダイナミック」である、なぜなら、`y`の値は変わりうるから)

spec `SpecUP`を定義しよう。
- disjunctive relationのsubaction Aを置き換えて定義するのだが、
- (4.6)とは異なっており、以下のように定義される
  - (4.10) `A^p == A /\ Pred_A(p) /\ NewPSet_A`
- 条件(4.9)に該当するような条件が必要である
  - `Pred_A(p)`を真にするような`p`の可能な値があることを主張するために
  - `p`は`Pi`の要素ではなく、`[Dom -> Pi]`となる関数であり、`Dom`は変わりうる
  - よって、我々の例では以下のように定義される。
    - (4.11) `SpecU => [] [\A <k;K> : A => (\E f \in [Dom -> \Pi] : Pred_A(f))]_vars`

`NextU`についても定義する。
- `Choose`
  - `p`は`Choose`についての予言をなにも作らない(`Pred_{Choose}(p)`は真)
    - `PredChoose(p) == TRUE`
  - `Choose^p`は、`p'[d]`が`Pi`の任意の値になることを許容する
    - `NewPSetChoose(p) == {f \in [Dom' -> Pi] : \A d \in Dom: f[d] = p[d]}`
- `Send`
  - 次のactionが`Send`であるなら`p`は予言しないと行けない。(`p[d] = "send`)
    - `PredSend(p) == p[x'] = "send"`
      - `x'`はactionによって送られる値
  - `Send` actionは`Dom`から要素`d`を取り去る(`d` に関して作られた予言 `p`は消される)
  - `Dom`の他のすべての要素については、`p[d]`の値は変わらずである。よって、以下のように定義される。
    - `NewPSetSend(p) == {[d \in Dom' |-> p[d]]}`
- `Rcv`
  - 予言なし
    - `PredRcv(p) == TRUE`
  - `Dom`への変更なし
    - `NewPSetRcv(p) == {p}` 
- `Undo(S)`
  - `p`が`S`のすべての要素が送信さないことを予言していた時に、`Undo(S)`は可能になる。
    - `PredUndo(p, S) == \A d \in S : p[d] = "undo"`
  - `p`が`Undo(S)`に関する予言を作った要素すべてについて、`Undo(S)`actionは`Dom`から取り除く
    - `NewPSetUndo(p) == {[d \in Dom' |-> p[d]]}`

これらによって、`SpecUP`を定義することができるようになる。
  `InitUP`と`NextUP`を含めて、`A^p`のsubactionsの用語を用いて
    (4.10)を使って
  `p`の初期値は、一意な、ドメインが空なfunctionである。
    - `[d \in {} |-> exp]`と書ける
    - `<>`(empty sequence)の方が簡単に書ける。

Refinement Mappingを作るよ
  `SpecUP` が Module`SendSet` の `Spec`を実装するようなのを
  `\overline{y}` を `p[d] = "send"`となるような`y`の要素`d`の集合にmappingするようなもの

そんなInstanceを作ろう。
そして、Theoremも作ろう。
このTheoremはTLCでチェックできる。

### subaction Aを含むnext-state関係の選言的な表現(disjunctive representation)の確認の問題点と経過悦作

(4.11)について、それぞれのsubaction Aについて成り立つことを示さないといけない。

```
[] [
  /\ Choose => (\E f \in [Dom -> \Pi] : PredChoose(f))
  /\ Send => (\E f \in [Dom -> \Pi] : PredSend(f))
  /\ Rcv => (\E f \in [Dom -> \Pi] : PredRcv(f))
  /\ \A S \in SUBSET y : Undo(S) => (\E f \in [Dom -> \Pi] : PredUndo(f, S))
]_vars
```

でもこの確認には問題がある
  TLCはmodule `SendSetUndoP`に対して、specification `SpcU`の振舞いを持つことを許していない
    なぜなら、そのspecは変数`p`についての振舞いを記述していないから

解決策1:
- moduleに変数`p`の宣言が表れる前のところで`==========`を挿入して、必要なモデルを作る

解決策2:
- module`SendSetUndo` に、変数`p`の宣言が表れる前に、すべての定義を写し
- そのspecに対するモデルにおける条件のチェックをする
  - これはエレガントではない。なぜなら、`SendSetUndo`のものではないから。

良い解決策:
- `SendSetUndoP`から定義を以下のmoduleに移す
- 新たな`SendSetUndo`を拡張してかつ、`SendSetUndoP`によって拡張されるmodule

これによって、条件を確認することができる

けどこの解決策の実施は退屈だから、代わりにmodule `SendSetUndoP`に放り込む

### 本節のまとめ

Section 4.1では、
- SendIntにおいては, one-prediction prophecy variable は次に送信される値を予言するのに使われていた
- SnedInt2では、値が受信されるまで次に送信される値を選ばなかった

このsectionで見たように
- それが必要になるまで、予言を後回しするように、array prophecy variableを使っていた
  - `Send` actionに`Dom`にempty setを設定するようにし
  - `Rcv` actionに`Dom`を`{"on"}`に設定するようにした。

## 4.4 Prophecy Data Structure Variables

最初は"one-prediction prophecy variable"をやった。
-> "arbitrary prophecy-array variable"へと一般化した。
-> "arbitrary prophecy data structure variable"へと更に一般化しよう。

作ったもの`SendSeq`:
- アイテムの集合ではなく、アイテムの列が選ばれるようなもの
- 変数 `y` の値は、データアイテムの集合ではなく、データアイテムの列になる
- 次に送られる値は、`y`の先頭にあるものになる。
  - 選ばれた値は`y`の末尾に追加される。

Undoも実装したもの `SendSeqUndo`
- sequence `y` から任意の要素を取り除くようなアクション
  - `RemoveEltFrom(i, seq)`を定義している; 
    - `seq`からi番目の要素を除外する
    - iは`1 <= i <= Len(seq)`とする。

`SendU` は `\EE y: Spec` を実装していることを示したい
- prophecy variable `p` は`y`の各要素が送信されるか"undone"になるかを予言する
  - これは、`p`が`y` と同じ長さの`Seq({"send", "undo"})`の要素になるようにすることでなす
- 各関数の中身についての確認
  - `Choose^p`: `p`のtailに"send"もしくは "undo"を追加
  - `Send^p`: `p`の先頭要素を取り除く
  - `Undo(i)`: `p`のi番目の要素を取り除く

SendSetでやったのと同じように、予言`Pred_A(p)`をそれぞれのsubactionsに対して定義していこう
  各subactionに対する`NewPSet_A`表現も定義する必要がある

`d`が`p`のdomain `Dom`で2つの連続する状態にある場合、
  `p[d]`は両方の状態の同じ予言を表炎する。
    しかし、これは今の例では真ではない。
      - Send stepで、`Len(p) > 1`とすると、状態`s`における`p[2]`で作られた予言は、状態`t`における`p[1]`によって作られた予言である。
      - Undo(i) stepの場合、(j > i)とすると、状態`s`における`p[j]`で作られた予言は、状態`t`における`p[j-1]`によって作られた予言である。
    (量化されているから、真ではないと言ってるのか？)

action は`p` の `Dom` と `p'` の `Dom'` の要素間の関係を定義する。

Domが変わるんだわ
-> `NewPSet_A`を直接定義しない。
    なぜなら、 `NewPSet_A`に属する式`p'`は以下を満たさねばならない。
    - `Dom'` の `d` が`A`に関する予言を作る`Dom`の要素`c`と一致するかどうか、もしくはいずれの要素とも一致しないかであるならば、`p'[d]`は`\Pi`の任意の値を仮定する
    - もし、`d`がAに関する予言を一切しない`Dom`の`c`に一致するなら、`p'[d]`は`p[c]`に一致する。


`Dom`と`Dom'`間(actionによって変わったもの)の要素の対応関係を形式的に表現、partial injectionを使って
  A "partial" function from a set U to a set V is a function from a subset of U to V
    element of [D --> V] for some subset D of U.
  An injection is a function that maps different elements in its domain to different values.

PartialInjectionsをTLA+で定義する(prophecy.tla)
```
PartialInjections(U, V) == 
  LET PartialFcns == UNION { [D -> V] : D \in SUBSET U}
  IN {f \in PartialFcns : \A x, y \in DOMAIN f : (x # y) => (f[x] # f[y])}
```

それぞれのsubactionに対するpartial injection `DomInj_A` が定義される
- `DomInjChoose == [d \in Dom |-> d]`
- `DomInjSend == [i \in 2..Len(y) |-> i - 1]`
- `DomInjRcv == [d \in Dom |-> d]`
- `DomInjUndo(i) == [j \in 1..Len(y)\{i} |-> IF j < i THEN j ELSE j - 1]`

prophery array variableの定義で使われているsubaction Aに対して、`DomInj_A`は以下のように定義される
- `DomInj_A == [d \in Dom \cap Dom' |-> d]`

(なんかidentity function やempty functionについて話しているけれど、使わないからいいや)

Prophercy Data Structure Exampleに戻るぞ
 `NewPSet_A`を `DomInj_A` と `PredDom_A` を使って定義するぞ
- `PredDomChoose == {}`
- `PredDomSend == {1}`
- `PredDomRcv == {}`
- `PredDomUndo(i) == {i}`

`NewPSet_A` 
- `d`は`Dom`の要素でかつ、`PredDom_A` にはいっていなくて、`Dom'` の `DomInj_A[d]`に対応する要素があるような`[Dom' -> \Pi]`の関数の集合と等しいもの
- module `Prophecy`にカプセル化する。
```
NewPSet(p, DomInj, PredDom) ==
  { q \in [DomPrime -> Pi] :
       \A d \in (DOMAIN DomInj) \ PredDom : q[DomInj[d]] = p[d] }
```

これによって、`ProphAction`が定義できる
  これで`A^p`を定義することを許す
```
ProphAction(A, p, pPrime, DomInj, PredDom,  Pred(_)) ==
  /\ A
  /\ Pred(p)
  /\ pPrime \in NewPSet(p,  DomInj, PredDom)   
```

`Undo`に関しては問題がある。
- Operator `ProphAction` requires its last argument, which represents `PredA`, to be an operator with a single argument.
- `PredUndo`は2つのargumentsを持っている。
  - `Op(p)` equals `PredUndo(p, i )`となるような`Op`を導入して、改めて定義する

これで、`SendSeqUndoP`が定義できる

あとは、Refinement Mappingを定義する
- `SpecUP`が`SendSeq`の`Spec`を実装するのを
- アイディア:
  - `\overline{y}`が`y`のsubsequence
    - `y`のsubsequenceで以下のようなもの
      - `p`が`"send"`と等しいsequenceの要素と一致するような要素のみを含んでいるようなもの
- 実際の定義は少しトリッキー
  - `yBar`というのを定義する
    - Rというlocal recursive 定義を使う。
    - `yseq`が任意のsequenceで、`pseq`が同じ長さのsequence
    - `R(yseq, pseq)`は`yseq`のsubsequence
      - `yseq` は `yseq[i]`　を含む iff. `pseq[i]` が `"send"`と等しい場合のみ.

つくられたtheoremはTLCがチェックすることが可能

## 4.5 Checking the Denitions

`Spec^p`を定義する方法を見せてきた
- state function `Dom`を定義して、
- next-tate actionのdisjunctive representationのsubaction `A`に対して、以下を定義
  - `Pred_A`
  - `DomInj_A`
  - `PredDom_A`

これらの定義が
`\EE p : Spec^p`が`Spec`と等しいことを
保証するような確かな条件であることを満たさなければならない。

### Pred_A

まずは、`Pred_A`について。
最初の条件は(4.11) `SpecU => [][\A <<k;K>> : A => ( \E f \in [Dom -> \Pi] : Pred_A(f))]_vars`。

module prophecy で`ExistsGoodProphecy(Pred(_)) == \E q \in [Dom -> Pi] : Pred(q)`と定義されている。

これにより、(4.11)は`Spec => [][A => (ExistsGoodProphecy(Pred_A))]_vars`と書ける。

Aが非-空なcontextを持つ場合にこの定義がどう使われるかを見る、
(4.11)が`UndoP(i)`を表現されるための条件は、
```
SpecU => [][ \A i \in Dom :
    Undo(i) => ExistsGoodProphecy(LAMBDA p : PredUndo(p, i ))]_vars
```

### DomInj_A

次に、context`<<k; K>>`のをもつaction `A` に対する `DomInj_A`の一般的な要求は、
`Spec => [][\A <<k;K>> : A => IsDomInj(DomInj_A)]_vars`である。
`IsDomInj` はoperator argumentを持っていないから、local definition, local LAMBDA expressionを要求されない。

### PreDom_A

最後に`PreDom_A`について。
`PredDom_A` は、 `p[d]` が `A`に関する予言を作っているような、`Dom`の要素`d`の集合と等しくならなければならない。
  このことは、`PredDom_A`に属していない任意の要素は`A`に関する予言を作らないことと等しい。
    `A` に関する予言を作ることは、`Pred_A`の値に影響を及ぼすことである、
      つまり、予言を作らないことは、値に影響を及ぼさないことである。

確認せよ: 
`Pred_A`の値が、`PredDom_A`に属さない任意の`d`に対する`p[d]`の値に依存されないのは、
以下の式が真のとき、かつその時に限る
- `\A q, r \in [Dom -> Pi] : (\E d \in PredDom_A : q[d] = r [d]) => (Pred_A(q) = Pred_A(r))`

### 追加要件

式が意味をなすことを保証するため、
`PredDom_A`が`Dom`の部分集合であるという明らかな要求を作ろう

`Spec => [][A => (IsPredDom(PredDom_A, Pred_A))]_vars`

`A` stepが非-空なcontextを持っている場合は、以下のようになる。
```
Spec => [][ \A i \in Dom :
    Undo(i) => LET Op(p) == PredUndo(p,i) 
               IN IsPredDom(PredDom_A, Op)]_vars
```
もしくは`Spec => [][ \A i \in Dom : Undo(i) => IsPredDom(PredDom_A, LAMBDA p: PredUndo(p,i))]_vars`。

### 要求をSpecに追加

`SendSeqUndo`に追加する。

同じことを`SendSet`でしたいと思う。けれど、TLCはチェックできない。
なぜなら、`SpecU`は変数`p`の値を明示しないから。
この場合は、`SendSetUndoP`の`p`の表現以前を別のmodule`SendSetUndo`の最後に入れるか、
`p`の表現以前のところに`=====`を追加するかのどちらかをしよう。

### まとめ

これらの条件が満たされているかは、prophecy variableを追加するときに確認しましょう。
prophecy variable付きのspecificationが求めているspecificationを実装しているかを確認する前に、
あなたの定義をデバッグする方法を提供している。

## 4.6 Liveness

これまではSafety Partの話だった。Liveness Partについても同様にprophecy variableを追加する。
3.5節でリマークしたように、これは通常ではないspecificationを産む、
  liveness propertyが、next-state actionのsubactionではないactionについてのfairness conditionを主張する

history variableとは違って、specificationの形式だけではなく、specificationsも奇妙になる。

`SendInt`のケースで考える
- `SendP` step で`p'`に `\infinity`を設定するようにする、つまり、新しい値は無限大が送信されると予言すると、halt (stutter forever) してしまう。
- Liveness Propertyを追加して、止まらないことを要求する。
  - けど、このLiveness Property自体は、`p'`に `\infinity`を設定しないなどの何かが実際に起きないことを要求しているわけではない。
  - このような奇妙さを、「式 `Spec` は not machine closedである」という
    - Liveness Propertyが、Livenessと同様にSafetyにも影響を及ぼす、ということを意味する

Non-machine closedなSpecは、システムが「如何に」動くかの記述には使われてはならない。
非常に稀なケースだが、システムが「何である」かを記述するかの最も良い方法ではある。

# 5 Stuttering Variables

## 5.1 Adding Stuttering Steps to a Simple Action

- 長針`h`と短針`m`のある時計の`Spec2`
- 長針`h`のみの時計`Spec1`

`\E m: Spec2 \euiv Spec1`であるはず。

Spec2がSpec1を含意していることを示すのは簡単。

Spec1が`\E m: Spec2`を含意しているような証明をすることのできるRefinement Mappingはない。
- 補助変数`s`をSpec1に追加して`Spec_1^S`を作らないといけない、以下のようなものを
  - 59回は`s`のみを変えて(hを変えず(stuttering))、
  - `h`を増やすようなもの

このような補助変数を `stuttering variable`という。

next-state action of Specs take "normal" steps
- satisfy the next-state action of Spec when s equals `\top` (usually read "top"),
  - some value that is not a positive integer
  - value of s in the initial state equals `\top`

`s` is set to a positive integer
- then, `Spec^s` allows only stuttering steps that decrement s
  - the variables of `Spec` unchanged
  - `s` counts down to zero, it is set equal to `\top` again.

ここでは"simple" subaction、contextが空なもの、をとる。

subaction `A` を action `A^s` で置き換える。

(5.3)(`NoStutter`)　`A^s == (s = \top) /\ A /\ (s' = s)`


action A のstepの後のstuttering steps に`initVal`(なんらかの正の整数であるような初期値)を追加する。

一般化する。
最小の`\bottom`をもつwell-dounded partial order をもつような任意の集合を取る。
(5.4) (`PostStutter`)
```
A^s ==
  IF s = \top
    THEN A /\ (s' = initVal )
    ELSE  /\ vars' = vars
          /\ s' = IF s = \bottom THEN \top ELSE decr(s)
```

stuttering stepsは`A` step の後ではなく前に追加することもできる。
これは`A` stepが可能になったときだけ。
(`PreStutter`)
```
(5.5) A^s ==
  /\ ENABLED A
  /\ IF s = \bottom
      THEN A /\ (s' = \top )
      ELSE  /\ vars' = vars
            /\ s' = IF s = \top THEN initVal ELSE decr(s)
```

これらの前と後のケースをいずれの場合でもできるようにするよう一般化することはできる。
が、やらない。
なぜなら、それはたまに要求されることであり、2つの分離されたstuttering variablesを導入するよりも有意義に簡単にするわけではないから。

## 5.2 Adding Stuttering Steps to Multiple Actions

we first consider 
- how to add stuttering steps before or after an action A 
  - that may have a nonempty context

We assume that (context 変数の値に依存しない)
- the set `\Sigma`, its `\bot` element, and the operator `decr` 
  - do not depend on the values of the context variables.

However, (context 変数の値に依存しうる)
- `initVal` may depend on them(context variables).

therefore we must make sure that
- `initVal` is evaluated with 
  - the values of the context variables 
    - for which the action `A` is "executed"

(5.4)のような前にstuttering stepを追加するのには問題ないが、
  (Since the stuttering steps do nothing but decrement the value of `s`,
   it makes no difference 
      for which value of the context variables 
        `A^s` is "executed" 
        when `s # \top`)
(5.5)のような後に追加するのは問題がある。

How to solve?
- `s`の 非-`\top`な 値(複数)を 以下2つを伴うレコードとする
  - a `val` component
    - that equals the value of `s` described in (5.5),
  - and a `ctxt` component 
    - that equals the tuple of values of the context 
      - when `initVal` is evaluated
    - 換言すると, `ctxt` is set by the `ELSE` clause in the second conjunct of (5.5).
      -  `s.ctxt` が the values of the `context` variables に等しくなるという条件は、
        -  a conjunct to the `THEN` clause として追加される、
          - `A` is executed only in that contextを確実にするために

stuttering stepをactionの前や後に追加する方法
- separate stuttering variablesを追加、もしくは
- stuttering array variableの導入。

しかし、stuttering stepは直前or即時に行われるから、
すべて同じstuttering variable `s`に追加できる。
  Stutering Stepは他のset `\Sigma`, its `\bot` element, and the operator `decr` を伴うsubactionに追加することが可能。
`s`の値は、stuttering stepが追加された先のactionを示す。
  How? `s`の非-`\top`な 値に、`id` componentを追加。
    `id` componentはstuttering stepが追加された先のactionを同定する。
      他のactionから区別できる。
      actionの名前と同様にする
    このcomponent が設定されるのは、when `s` is first set to a non-`\top` value,
    新たなsubaction `A^s`の実行が`s \noteq \top` の場合に可能になるのは、`s.id` が the identier of `A`に等しい場合のみ.

`PostStutter`と`PreStutter`は、`initVal = bot`の場合に一度だけstuttering stepを追加する。
が、複数回追加できるようなoperatorを使うのは時々便利になる。

Hourの簡単な例で考えよう。
  Nextは常にenabled。
  actionが1つなので、actionIdの振り方を考えなくていい。
  contextは空でいい。
  (あとは適宜埋めていけばいい。)

## 5.3 Correctness of Adding a Stuttering Variable

stuttering variable 追加したけれど、正しいのか？

`\EE s: Spec^s`が`Spec`を含意することは明らか。

stuttering stepsの無限列を追加する場合や、
`PreStutter`に間違った`enabled` argumentを追加した場合は、
等しさを示すことに失敗する。

`PostStutter`と`PreStutter` operatorsの全ての使用に対して、以下の条件を満たせば、等しさが示せる。

1. For every `\sigma` in `\Sigma`, the sequence of values `\sigma`, `decr(\sigma)`, `decr(decr(\sigma))`, ... is contained in `\Sigma` and eventually reaches `bot`.
  - (`StutterConstantCondition` として定義する。)
2. `initVal` is in `\Sigma`.
  - `Spec => [][\A <<k;K>> : A => (initVal \in Sigma)]_vars`
3. `enabled` is equivalent to `ENABLED A` [for `PreStutter` only]
  - `Spec => [](\A <<k;K>> : enabled \equiv ENABLED A)`

## 5.4 Adding Innite Stuttering

actionと関連していない、無限の数のsuttering stepsを追加するケースについて、完全さのために議論する。

内部変数が変わり続けるような、Refinement Mappingはあるか。
できない。だって、 `Spec1` で許されていて全ての振舞いが止まるなら、`Spec_1^a`( `Spec1`に補助変数`a`を追加したもの )で許されていた振舞いも止まるから。

解決方法: stutering variableを追加する。

Let 
- `Spec` equal `Init /\ [][Next]_vars`
- `UC` be the stuttering action `UNCHANGED vars`

Since 
- `[Next]vars` equals `Next \/ UC`,

we can write `Spec` as
- `Init /\ [][Next \/ UC]vars`

therefore, we can add the suaction `UC` to any disjunctive representation of `Next`

`s`をhistory variableで追加する、`UC` に含まれるdisjucntive representationを使って(cf: section 3)

これによって、`Spec^s`を定義できる。

`Spec^s == Init^s /\ [][Next^s]_<<vars, s>> /\ WF_<<vars, s>>(UC^s)`

` WF_<<vars, s>>(UC^s)` は`s`のみを変える。

histroy variableとして追加したから、
`\EE Init^s /\ [][Next^s]_<<vars, s>>` は `Spec`に等しい。

だから、`\EE s : Spec^s` は`Spec`に等しい。

## 5.5 Liveness

stuttering variableを追加してもLivenessは何も問題ない。
5.4で述べたように、`s`以外の値を変えないから。

`Spec^s`は一般的ではない形式を持っているかもしれないが、それは異様なものではない。

`Spec`がmachine closedなら`Spec^s`もmachine closed。
しかし、`Next^s`のsubactionsにのみfairness condition付きのstandard formにそれを追加することは、
history variableに対しておこなったほどシンプルではない。

# 6 The Snapshot Problem

`single-writer atomic snapshot memory`, `snapshot object`について、Afekらの研究したアルゴリズムについて、
そのシンプルなバージョンのアルゴリズムについて、補助変数を使ってチェックする。

## 6.1 Linearizability

an atomic read of an array of memory registersの実装に使われるアルゴリズム
  このspecification は、data objectのlinearizable specificationの特殊ケース

data object、state machineとも呼ばれる、は、ユーザープロセスからコマンドを実行する。

`Apply(i, cmd, st)`:
- the output and new state of the object 
  - that results from process `i` 
  - executing command `cmd` 
  - when the object has state `st`
- A record with `output` and `newState` fields describing 
  - the result of process `i` executing command `cmd` when the object is in state `st` .

- `Procs`: The set of processes.
- `Commands(i)`: The set of commands that process `i` can issue.
- `Outputs(i)`: The set of outputs the commands issued by process `i` can produce.
- `InitObj`: The initial state of the object. 

A linearizable implementation of the data object is
  one in which the state of the object is internal,
    the only externally visible actions being the issuing of the command and the return of its output.

1. `BeginOp(i, cmd)` step: externally visible
2. `DoOp(i)` step: modifies the state of the object, modifies only internal variables -- including an internal variable describing the state of the object.
3. `EndOp(i)` step: externally visible

"steps are externally visible" means that they modify externally visible variables

To simplify the specication, we assume that the sets of commands and of outputs are disjoint.
We can then use a single externally visible variable `interface`,
- letting `BeginOp(i, cmd)` set `interface[i]` to the command `cmd` and 
- letting `EndOp(i)` set it to the command's output.

introduce an internal variable `istate` 
- to hold the internal state of the processes
- letting `BeginOp(i, cmd)` set `istate[i]` to `cmd`, and 
- letting `DoOp(i)` set it to the command's output.

Initially, `interface[i]` and `istate[i]` equal some output, for each `i`

Fairness Conditionとかも追加する。

`LinearAssumps`という仮定も追加している。
これは、インスタンス化されたコンスタンツが以下の性質を満たすことをチェックするため
- それら(Constants)が、moduleに対して、linearizable objectを特定するようにするため？
(to check that the instantiated constants satisfy the properties they should for the module to specify a linearizable object.)

all those propertiesを記述するために、
`ObjValues`を導入:
- to describe the set of all possible states of the object.


以下の定義は、`ObjValues`を導入するのと等しい。等しさを示すのは集合論の良い練習問題になるとのこと。
```
ObjValues  == LET ApplyProcTo(i, S) == {Apply(i, cmd, x).newState : x \in S, cmd \in Commands(i)}
                  ApplyTo(S) == UNION {ApplyProcTo(i, S): i \in Procs}
                  ApplyITimes[i \in Nat] == IF i = 0 THEN {InitObj}
                                                     ELSE ApplyTo(ApplyITimes[i-1])
              IN UNION {ApplyITimes[i]: i \in Nat}
```

## 6.2 The Linearizable Snapshot Specication

"a snapshot object" で意味するのは `atomic snapshot memory` とAfekらが読んでいたもの。

In a snapshot object, the processes are either readers or writers.

A snapshot object is an array of registers, one per writer.

A write operation:
- writes a value to the writer's register and 
- produces as output some fixed value that is not a possible register value. 

A read operation:
- has a single command that produces the object's state as output and 
- leaves that state unchanged.


four constants:
- `Readers`: the set of writer processes
- `Writers`: the set of reader processes
- `RegVals`: the set of possible register values
- `InitRegVal`: a value in `RegVals` that is the initial value of a register

`Linearizability` を使うので、`object`の代わりに`memory`という名前を使う。

We define 
- `NotMemVal` be the single reader command and 
- `NotRegVal` to be the single write command output.

## 6.3 The Simplied Afek et al. Snapshot Algorithm

`imem`という内部変数を使う
- 値は`imem[i]`の配列で、それぞれ以下の2つを持っている
  - i番目のregisterの値
  - そのregister が何度書き込まれたかの数字を値にするinteger

仮定: 全体のペアは、アトミックに読み込まれ書き込まれうる

write operationがregisterに値`cmd`を書き込む方法:
- `DoOp(i)` actionが`imem[i]`に`<<cmd, imem[i][2]+1>>`とする

read operationがやること
- まず scan procedure
  - 任意の順序で、一度`imem[i]`の全ての要素を読む
  - 任意の順序で、二回目にそれらを読む
  - もし任意の`i`について両方とも同じ値を読んだのであれば、それは、読んだ、register 値の配列を出力する
    - いずれかの`i`で異なる値が得られれば、出力を生成せず、procedureは続けられる。
    - 値が出力されるまでは、延々とscan procedureは繰り返される。

このscan procedureは停止しない。だから、Livenessの要求を満たせないが、Safety Partは満たせる。
実際のアルゴリズムは、ある値`i`に対して、`imem[i]`に対して三つの異なる値が読み込まれたときに、出力を生成する方法を持っている。これを使えば、readの停止性も保証できる。
ただし、これは複雑で、よって、Refinement Mappingもより複雑で、model checkもより時間がかかる。
だから、シンプルなバージョンで話を進める。

`MemVals`, `InitMem`, `NotMemVal`, `NotRegVal`, これらについては定義は同じ。

```
IRegVals == RegVals \X Nat
IMemVals == [Writers -> IRegVals]
InitIem == [i \in Writers |-> <<InitRegVal, 0>>]
```

variable `imem` について、
- `imem[i]` は `RegVals \X Nat` の要素(上記の`imem`の説明と対応)。
  - first component: representing `mem[i]`
  - second component: the number of times mem[i ] has been written.

variable `wrNum` について、
- domain: `Writers` 
- `wrNum[i]`: `BeginWr(i)`step が実行された数

vbariables `rdVal1`, `rdVal2`
- `rdVal1[i]`, `rdVal2[i]`のは、reader`i` によってscan procedure で読みこまれた値のこと
- 初期値は空`<<>>`

wrtier action は簡単。
補足: because 
1. wrNum[i] counts the number of BeginWr(i, cmd) steps and
2. imem[i][2] is set to wrNum[i] by the DoWr(i)
,
when imem[i][2] equals wrNum[i]
- EndWrite(i) action should be enabled and 
- DoWr(i) disabled 
.

read action
`BeginRd(i)`は簡単。

scan procedure

`AddToFcn` を使う。

Rd1とRd2を定義する。

TryEndRdを定義する。
Rd1の結果とRd2の結果を比較し、
等しければreadに対する`EndOp`を実行し、
そうでなければ、また次のscanを始められるようにする。

## 6.4 Another Snapshot Specication

Let `SpecA` be the algorithm's specification and 
let `SSpecL` be the specification `SafeSpec` of `LinearSnapshot`.

`AfekSimplied` が任意のRefinement Mapping下にあって、`LinearSnapshot`のSafety Specificationを実装していないことを示す。
  -> 矛盾が生じるからRefinement Mappingがありえない。
    以下のような、ケースで`\overline{istate}[i][j`の値が異なることになる。
    - (Step1) `BeginRd(i)` -> `Rd1` -> `Rd2` -> 
    - (Step2) Writer `j` does a complete write operation -> 
    - (Step3) `TryEndRd(i)`

`\overline{DoRd(i)}` step が 
`\overline{DoWr(j)}` step より前に生じるように、
`mem` と `isate` の値を選ばなければならない。
  この選び方は `\overline{DoWr(j)}` step の後に何のstepが起きるかを知っていることを要求する
  -> Prophecy variable を追加する

prophecy variableを追加しない方法: output valueを選択する前に、できるだけreader に待機させる。
`SpecNL` 
- that allows the same externally visible behaviors as specification `SpecL` of `LinearSnapshot`; 
- and whose safety specication `SSpecNL` allows the same visible behaviors as `SSpecL`.
- in `SpecNL` we make a reader wait as long as possible before choosing its output value.

依然として、
`SSpec_NL`が`SSpec_L`と同じようなexternally visible behaviorを許されていることを示すためには、
prohecy variableが必要。

`Spec_NL`の利点:
- prophecy variableが複雑だから、それを避けれる

internal stateにmemory `mem`（read operationが返すことを許されている）の全ての値をレコードする。
internal state は、過去において何が起きたかを記憶している。
-> `SpecNL` will require adding a history variable to the algorithm's spec.

- `wstate` : `wstate[i]` is the same as the value of `istate[i]` in `LinearSnapshot`,
- `rstate` : 
  - `rstate[i]` is the sequence of values that `mem` has assumed thus far while the operation has been executing.
  - The first element of `rstate[i]` is therefore the value `mem` had when the `BeginRd(i)` step occurred
  - The value of `rstate[i]` is the empty sequence <<>> when `i` is not executing a read operation.

あとは良しなに`LinearSnapshot`の定義を拡張して、作っていけばできる。

## 6.5 NewLinearSnapshot Implements LinearSnapshot

略記:
- `S_{L} == \EE mem, istate : Spec_{L}`
- `S_{NL} == \EE mem, rstate, wstate : Spec_{NL}`

`Spec_A` implements `S_L`を証明したい。
だから、
- `Spec_A` implements `S_{NL}` (6.6節で証明)
- `Spec_{NL}` implements `S_L` (本節6.5説で証明)
を示す。

To show that `S_NL` implements `S_L`, 
we add to `Spec_NL` a prophecy variable `p` then a stuttering variable `s` 
  to obtain a specication `Spec^{ps}_{NL} `
    such that `\EE s, p : Spec^{ps}_{NL}` is equivalent to `Spec_NL`.
We then show that `\EE s; p : Spec^{ps}_{NL}` implements `S_L` 
  by showing that `Spec^{ps}_NL` implements `Spec_L` 
    under a suitable refinement mapping `mem <- \overline{mem}`, `istate <- \overline{istate}`.

pとsについて
- `p`: prophecy variable to predict 
  - for each reader `i` which element of the sequence of memory values `rstate[i]` will be chosen as the output.
- `s`: stuttering variable;
  - A single stuttering step after a `BeginRd(i)` step if `p[i]` predicts that the read will return the current value of memory.
  - Stuttering steps after a `DoWr(i)` step
    - that will implement the `\overline{DoRd(j)}` step of every current read operation 
    - that returns the value of `mem` immediately after the `DoWr(i)` step.

### 6.5.1 Adding the Prophecy Variable

It is most convenient to define `p` in terms of a disjunctive representation 
  in which `EndRd(i)` is decomposed into `\E j \in 1 . . Len(rstate[i]) : IEndRd(i, j )`
(どこらへんが便利になるんだ？)

A prediction is made for reader `i` when the element `i` is added to `Dom`, 
  which is done by a `BeginRd(i)` step.
The prediction is used by the `IEndRd(i, j)` action.

予言するから定義しないと。
The definitions of `PredA`, `PredDomA`, and `DomInjA` for the subactions `A`

The module next defines the temporal formula `Condition`, which should be implied by `Spec`.

TLCは`\EE p: SpecP` が`Spec`に等しいことを証明できる。

### 6.5.2 Adding the Stuttering Variable

We need to add a single stuttering step after a `BeginRdP(i)` step 
  iff the reader will output the current value of `mem`,
    which is the case iff the step sets `p[i]` to 1.

We also need to add a stuttering step after `DoWrP(i)` 
  for every currently reading reader `j` for which `p[j]` predicts 
    that the value of `mem` that the step appends to `rstate[j]` is the one that the read will output.

`SpecPS`を作るにあたっては、
`Spec => [][\A <<k;K>> : A => (initVal \in Sigma)]_vars`の条件もある。

TLCでチェック可能

`ASSUME`ステートメントを追加して、`MayPostStutter`に対してコンスタントコンディションをチェックするため、
stuttering stepsが追加されるのに使われているか

### 6.5.3 The Renement Mapping

6.5 で述べたこと
> We then show that `\EE s; p : Spec^{ps}_{NL}` implements `S_L` 
>   by showing that `Spec^{ps}_NL` implements `Spec_L` 
>     under a suitable refinement mapping `mem <- \overline{mem}`, `istate <- \overline{istate}`.

`mem`はそのまんま。

`\overline{istate[i]}`については、
writer `i`の場合は、`wsate[i]`に等しくすればよいが、
reader `i` に対しては、問題がある。

`SpecL`において, readもwriteも実行していないany process `i`に対して , `istate[i]` equals `interface[i]`.
だから、現在読まれていない任意の reader `i` に対して、`\overline{istate[i]}`は `interface[i]` に等しい。
現在読み込まれている場合、
- `\overline{istate[i]}`は `interface[i]` に等しいのは正しい、iff. `rstate[i] # <<>>`
  - これが意味するところは、`p[i]` がpositive integer であること

これには2つの可能性がある。
- `p[i] = 1`
  - `DoRD(i)`stepは シミュレートされる、 `BeginRd(i)`に付け加えるstuttering step によって
  - `\overline{istate[i]}`は `rstate[i][1` に等しいのは正しい、iff. `rstate[i] # <<>>`
    - `BeginRd(i)`の後や、直後にstutterging stepが付け加えられる前を除く
- `p[i] > 1`
  - `DoRD(i)`stepは シミュレートされる、 `DoWr(j)`に付け加えるstuttering stepsのいずれかによって
  - `\overline{istate[i]}`は `NotMemVal` に等しい、`p[i] <= Len(rstate[i])`の限り
    - ただし`i`が`s.val`の要素である場合はそうではない。

`istateBar`を定義する。

theoremはTLCによってチェック可能である。

これで、`SpecPS`が`LS!Spec`のsafety part と Liveness partの両方を満たすことを示せる。

## 6.6 AfekSimplied Implements NewLinearSnapshot

6.5節で述べたこと
- `Spec_A` implements `S_{NL}` (6.6節で証明)

history variableを追加したら、Refinement Mapping作れる。
  `Spec_NL`のrstateを記録するために。

実装は単純
  Note:`memBar`を使っている定義は、`mem`を使っている
  `memBar`が`imem`から得られたmemory value と等しくなるようにmoduleは定義している、
    `memBar[i]`が`imem[i]`の最初の要素と等しくなるようにして

あとはrefinement mappingを作る。

TLCでチェックすることができる。
