package DLprover

import java.net.InetAddress


object Runner {


  def write_file(in: java.io.InputStream, fn: String): Unit = {

   val br = new java.io.BufferedReader(new java.io.InputStreamReader(in))

   val out_stream = new java.io.PrintStream(
     new java.io.FileOutputStream(fn))

   var ln = br.readLine()
   while (ln != null ){
     out_stream.println( ln)
     out_stream.flush
     ln = br.readLine()
   }

   out_stream.close

  }



  def main(args: Array[String]) {

    println( System.getProperty("user.dir"))

    if (args.length != 2){
      println("two arguments: number of workers and problem name")
      exit(0)
    }

    val n = Integer.parseInt(args(0))
    val prob = args(1)

    val scala_home ={ 
      val sh = System.getenv("SCALA_HOME")
        if (sh == null) 
          {throw new Error("please set the SCALA_HOME variable")}
        else sh
    }

    val jlink ={ 
      val jl = System.getenv("JLINK")
        if (jl == null) 
          {throw new Error("please set the JLINK variable")}
        else jl
    }





    val cp = 
      "-classpath .:"+
      scala_home + 
       "/lib/scala-library.jar:"+
       "./commons-cli-1.2/commons-cli-1.2.jar:" +
      jlink +
      "/JLink.jar"


    val my_ip = InetAddress.getLocalHost().getHostAddress()

    println(my_ip)


    val rt = Runtime.getRuntime()

    val coor_pb = new ProcessBuilder(
      "./redirect", 
      "java " + cp + " banyan/Coordinator", 
       "out/coor.out", "out/coor.err ")
    val coor = coor_pb.start()

    val ns = (1 to n).toList

    val ps = ns.map(i =>
      {val worker_pb =
        new ProcessBuilder(
        "./redirect",
              "java " + cp + " banyan/Worker " + " -c " + my_ip + 
              " -cp 9500 " + " -p " + (50000 + i), 
              "out/worker" + i + ".out", "out/worker"+ i +".err")
       worker_pb.start()})
       

    val client_pb = new ProcessBuilder(
             "./redirect", "java " + cp + " DLprover/Client "
              + " -c " + my_ip + " -cp 9500 " + " -p " + 49999 + 
              " -prob examples/simple.dl", 
              "out/client.out", "out/client.err")

    val client = 
      client_pb.start()



    Thread.sleep(1000)


    coor.waitFor()

    val ds = ps.map(_.destroy)

    coor.destroy()

    



    ()

  }




}
