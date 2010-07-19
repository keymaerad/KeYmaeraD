package DLprover

import banyan._

import scala.actors.Actor
import scala.actors.AbstractActor
import scala.actors.Actor._


import scala.actors.remote.RemoteActor
import scala.actors.remote.RemoteActor._
import scala.actors.remote._


import org.apache.commons.cli.Options
import org.apache.commons.cli.CommandLine
import java.net.InetAddress


object Client {


  def parse(args: Array[String]) : CommandLine = {

    //use CLI to parse command line options
    var opts = new org.apache.commons.cli.Options();
    opts.addOption("c", true, "coordinator address");
    opts.addOption("cp", true, "coordinator port ");
    opts.addOption("p", true, "port the client should run on");
    opts.addOption("prob", true, "pathname to root problem to solve.");

    //do parsing
    var parser = new org.apache.commons.cli.GnuParser();
    parser.parse( opts, args);

  }


  def main(args: Array[String]) {

    import BanyanClient._

    System.err.println("client says: hello world.")

    val cmd = parse(args)

    if (!cmd.hasOption("c")) {
      println("Forgot to supply coorr address. (use -c). Quitting.")
      System.exit(0);
    }

    if (!cmd.hasOption("cp")) {
      println("Forgot to supply coor port. (use -cp). Quitting.")
      System.exit(0);
    }

    if (!cmd.hasOption("p")) {
      println("Forgot to supply client port. (use -p). Quitting.")
      System.exit(0);
    }

    if (!cmd.hasOption("prob")) {
      println("Forgot to supply problem. (use -prob). Quitting.")
      System.exit(0);
    }

    setCoordinator(cmd.getOptionValue("c"), 
                   Integer.parseInt(cmd.getOptionValue("cp")))
    setLocalPort(Integer.parseInt(cmd.getOptionValue("p")))

    val inp = 
     io.Source.fromFile(cmd.getOptionValue("prob")).getLines.reduceLeft(_+_);
    
    val g0 = 
      P.sequent_parser(inp) 

    val g1: Sequent = g0 

    val rootNode = new OrNode(g1)

    startRoot(rootNode)


  }




}
