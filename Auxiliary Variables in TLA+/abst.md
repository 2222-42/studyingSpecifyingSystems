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
