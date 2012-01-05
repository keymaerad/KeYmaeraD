/* a NAV instance generator 
   see: A. Fehnker and F. Ivancic, Benchmarks for Hybrid System Verification, 2004. [http://www.cse.unsw.edu.au/~ansgar/papers/bench.pdf]
   use a JavaScript >=1.6 interpreter, e.g. V8
*/

/* Parameters
   NAV being the map of fields
   A   being the differential equation matrix
*/
var NAV = [[-2, 2, 4],
           [ 4, 3, 4],
           [ 2, 2,-1]];
var A = [-1.2,0.1,0.1,-1.2];

/* Generator
*/
var forb;

function vdize(i,key) {
  if(i===-2) forb = key;
  if(i<0) return false;
  var AP = 10000;
  //function round(n) { return ((n*AP)|0)/AP}
  function round(n) { return "("+((n*AP)|0)+"/"+AP+")"}
  return [round(Math.sin(i*Math.PI/4)),round(Math.cos(i*Math.PI/4))];
}

function println(msg){print(msg+"\n")}

function field(i) {
  return "x1>="+(i%3)+" & x1<="+((i%3)+1)+" & x2>="+((i/3)|0)+" & x2<="+(((i/3)|0)+1);
  }

function toStr(vd,i){
  function quot(i) {return "("+(i*10)+"/10)"}
  function opize(n){return n<0?"- "+n.toString().substring(1):"+ "+n}
  var diffEq = "v1' = "+quot(A[0])+"*(v1 "+opize(vd[0])+") + "+quot(A[1])+"*(v2 "+opize(vd[1])+") , "+
               "v2' = "+quot(A[2])+"*(v1 "+opize(vd[0])+") + "+quot(A[3])+"*(v2 "+opize(vd[1])+")";
  return "{"+diffEq+"; "+field(i)+"}";
         
}

var hp = NAV.reduce(function(a, b){return a.concat(b);}).filter(vdize).map(vdize).map(toStr).reduce(function(a,b){return a+" ++\n"+b});

forb = "~("+field(forb)+")";

print("{}\n"+forb+"\n|-[{\n"+hp+"\n}*]"+forb);

