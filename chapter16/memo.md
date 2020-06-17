# 16

## 16.1

### memo

"[tlaplus] About the behavior of RandomElement on refinement proofs" より。

> But then, when doing model checking and simulations, i observed CHOOSE was always selecting the first of the concrete model values. 

とのSolsonaから報告があり、質問者はRandomElementを利用するようにしたとのこと。

しかし、その場合、TLAPSでは証明できるが、TLCでのモデル検査で失敗するとのこと。

Stephanの回答

> You want to use existential quantification for non-deterministic (arbitrary) choice. CHOOSE is deterministic, and randomization is useful for testing, but is not what you want for proofs (unless you consider probabilistic systems, but then TLA+ is not the method of choice).

- `CHOOSE x` はDeteministicで、
- `\E x` はNonDeterministicである。
- `randomization`はテストには有効。

16.1.2では、任意の値と書いているが、TLCでの実行では必ずしもそうではないようだ。

証明したいことを見極めれば、Existential Quantificationの利用が望ましい。
