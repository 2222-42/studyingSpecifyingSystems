# Chapter14

## Comments

### How to implement Timeout

Timeoutの発想は、ABSpecのLoseと同じように、メッセージをなくすものである。

だから、Nextでの選言に入れてあげればTimeoutと類似の調査はできる。もちろん、実際のプロトコルを調査したいなら、さらに前提条件を追加する必要があるが。

(cf: https://groups.google.com/g/tlaplus/c/mvrg99_xc74?pli=1)

#### If Timeout Action Not Non Deterministic

cf: `[tlaplus] How to get rid of the  negative influence of  a  cycle timer mechanism`

Earnshaw の意見：
> But in my case, the timeout action is periodically happened, it used to trigger state sync operation to the whole cluster periodically , so it is always enabled as long as the node is not faulty.

Tickを使って、Timeoutアクションは、全体のクラスターに対してStateSyncOperationを送るのに使いたい。

Stepahnの回答：
> The benefit of modeling timeouts non-deterministically in this way is that you get rid of the Tick variable and the associated blowup of the state space.

> If the network is modeled using sets (i.e., unordered messages without duplicates), resending a sync messages will just lead to the same state being revisited and will have essentially zero cost.

Tickは本質的ではない。
Timeoutを非決定的にモデリングすることのメリットは、Tickを削り、State Spaceの爆発を避ける。

ネットワークが集合を使ってモデル化されているなら、
同期メッセージを送ることはただ同じStateに再度至ることを導くだけであり、
本質的にはゼロコストしかない。

## Questions

`constraint`の有効化ってどうするんだ？
-> 自分が写経したSpecで`Constant` と `Constraint`を間違えている個所があった
-> ToolboxではSpecOptionで指定できるから、それを使うこと
