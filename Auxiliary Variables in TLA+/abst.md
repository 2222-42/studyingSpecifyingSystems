# 1 Introduction

implementations は Higher-level specificationが要求していることを満たす
- Specの中におけるHigher-level conceptsが、Lower-level のimplementationされたデータ構造でいかに表現されているかを説明すること

このアプローチの歴史：

- Sequential Systemの領域でHoareの命名: `abstraction function`
- Concurrent Systemsに一般化した場合のAbadiとLamportの命名: `refinement mapping`
  - refinement mappingを構成するときは、補助変数(`auxiliary variable`)をimplementationに追加する必要があるかも。
    - 補助変数(`auxiliary variable`)は実際の変数の振る舞いに影響を与えず、かつ、実装(implement)する必要はないもの

本論文の目的：
- 補助変数をTLA+ Specificationsにどうやって追加するかを学ぶ

筆者の期待：
- 如何にしてSpecificationsに補助変数を追加する方法を学ぶにあたって、既存のspecificationsを慎重に学んでいる必要がある

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

Make a simple, useless example. The server responds to each input value i with one of the following outputs:

- `Hi` if i is the largest number input so far, 
- `Lo` if it's the smallest number input so far, 
- `Both` if it's both, and
- `None` if it's neither.

## 2.1 Specication MinMax1

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

- a behavior is a sequence of states
- a state is an assignment of values to all possible variables

2つの変数：

- the externally visible or observable values of the specication
- internal variable.

Internal Variableは`\EE`で書くことができる。

- `F`: temporal formula
- `v`: variable

Defiition of `\EE v: F`:

厳密な定義は複雑なので、単純に説明すると, behavior `\sigma` satisfies `\EE v: F` 
iff there eists a behavior `\tau` s.t.
- `\tau` satisfies `F`
- `\tau` is identical to `\sigma` except for the values its states assign to `v`

> The operator `\EE` is much like the ordinary
existential quantier `\E` except that `\EE v : F` asserts the existence not of a single
value for `v` that makes `F` true but rather of a sequence of values, one for each state
in the behavior, that makes `F` true on the behavior.

MinMax1で`\EE y: Spec`を導入しない理由：

- `y` が `Spec`の定義の中に表れていて、式がillegalになるから

e.g., `{v \in exp : v^2 > 42}`という表現は、`v`がすでに宣言もしくは定義されているModuleの中では許容しない。

hidden variable `v`を含む`Spec`の式を書く方法(ways to write the formula `Spec` with `v` hidden in TLA+.):

1. MinMax1を生成する別のモジュールを書く

別のモジュールを書くのは、TLA+ tools は `\EE` を含むspecificationをチェックできないから。(there's little reason to do it since the TLA+ tools cannot check specications written with `\EE`)
TLAPSは場合によってはできる。

別のモジュールを書く方法：

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

> The specication of our system in module MinMax1 uses the variable y 
to remember the set of all values that the user has input.

> Module MinMax2 species the same user/server interaction that 
remembers only the smallest and largest values input so far, 
using the variables min and max.

Module MinMax1ではy を使って、ユーザーが入力した全ての値の集合を記憶していた。
Module MinMax2では、同じユーザー/サーヴァーの相互作用は、入力された最小と最大の値のみを保存する。保存については変数minとmaxを使う。

The philosophically correct specification, which hides the internal variables min and max, is \EE min; max : Spec .

#### 疑問点

なんで今度は`\EE`が導入できるの？

MinMax1で`\EE y: Spec`と書けなかった理由は、
`y` が `Spec`の定義の中に表れていて、式がillegalになるからということだった。

MinMax2での`min`と`max`はどうか？

変数としては表れている。

yの初期値は`{}`と空集合で定義されている。
minとmaxの初期値はInfinityとして独自に定義している。

`setMin(y')`などがなくなった。
結局`x = min'`などで見ると、y'を使っているのと代わりないように思える。

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
