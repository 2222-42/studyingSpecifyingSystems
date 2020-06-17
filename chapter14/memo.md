# Chapter14

## Comments

### How to implement Timeout

Timeoutの発想は、ABSpecのLoseと同じように、メッセージをなくすものである。

だから、Nextでの選言に入れてあげればTimeoutと類似の調査はできる。もちろん、実際のプロトコルを調査したいなら、さらに前提条件を追加する必要があるが。

(cf: https://groups.google.com/g/tlaplus/c/mvrg99_xc74?pli=1)

## Questions

`constraint`の有効化ってどうするんだ？
-> 自分が写経したSpecで`Constant` と `Constraint`を間違えている個所があった
-> ToolboxではSpecOptionで指定できるから、それを使うこと
