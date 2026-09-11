import Tex2lean.Model.Prior
import Tex2lean.Model.Pseudocode
import Tex2lean.Meta.ModelClosure

\bp Assume that $a$ is Drazin invertible in $A.$ Then there exists
$b \in A $ and $ k \in \mathbb{N}$ such that $ bab=b, ab=ba,
a^kba=a^k.$ Without lose of generality, we can assume that $k=1.$
Let us show that $ A= aA \oplus N(a).$ Since $ aba=a,$ we have $
aA= a^2 A.$ So if $x \in A,$ then $ ax= a^2t, $ with $ t\in A.$
Hence, $ a(x- at)=0$ and $ x - at \in N(a).$ Therefore, $ x= at +
(x-at).$ Moreover, if $ x \in aA \cap N(a),$  then $ x=at,t \in
A.$ Hence, $ 0= bax= abat= at=x.$   Thus, $ A = aA \oplus N(a).$
\ep

\noindent Conversely, assume that $ A= aA \oplus N(a).$ Then there
exist $ p \in aA,  q \in N(a),$ such that $ e=p+q.$ Then $p= p^2 +
qp$ and $p-p^2= qp.$ As $ aA \cap N(a) = \{0\},$ it follows that
$p^2= p$ and $qp=0.$ Similarly, we can show that $q^2=q$ and $
pq=0.$ Moreover, if $ x\in A,$ then $x= ex= px+ qx.$ As $pA \cap
qA= \{ 0\},$ we have $ A= pA \oplus qA.$ Thus, there exist $ r \in
A,$ such that  $a=pr$ and hence $pa= p^2r= pr=a.$ On the other
hand, we have $ ap= a(e-q)= a.$ Thus $ap=pa=a.$ Similarly, we have
$ aq=qa=0.$
 Since $ A= aA \oplus N(a),$ it follows that $aA= a^2A.$ So there
exist $ b \in aA,$ such that $ p= ab.$ Then $ a= pa= aba.$ We have
$ a(ba-p)= aba-ap=  0,$ so $ ba-p \in aA \cap N(a).$ Thus $ba=p$
and $ ba=ab=p.$ As $ bab- b= (ba-e)b= qb \in aA \cap N(a),$ we
have  $bab=b.$ Finally, we have $aba=a, bab=b, ab=ba$  and $a$ is
Drazin invertible in $A.$

#modelClosureOfType bFredholm_prop_2_4

#print axioms bFredholm_prop_2_4

end Tex2lean.Model
