/* a NAV instance generator 
   see: A. Fehnker and F. Ivancic, Benchmarks for Hybrid System Verification, 2004. [http://www.cse.unsw.edu.au/~ansgar/papers/bench.pdf]
   use a JavaScript >=1.6 interpreter, e.g. V8
*/

/* Parameters
   NAV being the map of fields
   A   being the differential equation matrix
   AP  being the real numbers precision
*/
var NAV = [[-2, 2, 4],
           [ 4, 3, 4],
           [ 2, 2,-1]];
var A = [-1.2,0.1,0.1,-1.2];
var AP = 10000;

/* Generator
*/
var forb;

function vdize(i,key) {
  if(i===-2) forb = key;
  if(!i || i<0) return false;
  function all(n) {
    function quot(n) {
      var divisor = (n+"").indexOf(".");
      if(divisor<0) return n+"";
      divisor = Math.pow(10,(n+"").length-divisor);
      return "("+(n*divisor)+"/"+divisor+")";
    }
    function round(n) { return ((n*AP)|0)/AP}
    return quot(round(n));
    }
  return [all(Math.sin(i*Math.PI/4)),all(Math.cos(i*Math.PI/4))];
}

function println(msg){print(msg+"\n")}

function field(i) {
  return "x1>="+(i%3)+" & x1<="+((i%3)+1)+" & x2>="+((i/3)|0)+" & x2<="+(((i/3)|0)+1);
  }

function toStr(vd,i){
  if(!vd) return vd;
  function quot(i) {return "("+(i*10)+"/10)"}
  function a(n){return n<0?"- "+n.toString().substring(1):"+ "+n}
  var diffEq = "v1' = "+quot(A[0])+"*(v1 "+a(vd[0])+") + "+quot(A[1])+"*(v2 "+a(vd[1])+") , "+
               "v2' = "+quot(A[2])+"*(v1 "+a(vd[0])+") + "+quot(A[3])+"*(v2 "+a(vd[1])+") , "+
               "x1' = v1 , x2' = v2";
  return "{"+diffEq+"; "+field(i)+"}";
}

var hp = NAV.reduce(function(a, b){return a.concat(b);}).map(vdize).map(toStr).filter(vdize).reduce(function(a,b){return a+" ++\n"+b});

forb = "~("+field(forb)+")";

print("{}\n"+forb+"\n|-[{\n"+hp+"\n}*]"+forb);

