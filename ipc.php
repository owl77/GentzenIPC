<!DOCTYPE html>
<html>

<style> p { font-family:'Courier New' }
    .center { margin:auto; width:80%; border:1px solid grey; padding-left:20px;}
    .center2 { margin:auto; width:75%; border:0px solid grey; padding-left:30px;}
</style>





<body style="background-color:lightblue; font-family:'Courier New'">
<br>
<br>



<br>



<br>
<br>
<div class="center">
<form action="ipc.php" method="post">
<br>
<textarea style="width:770px;height:450px;font-family:'Courier New';font-size:16px"  id="output"  name="output" >
<?php

if($_POST["form"]!="" && $_POST["dep"]!=""  ){
$f = "'".$_POST["form"]."'";
$d = $_POST["dep"];
$com = "python ipc.py ".$f." ".$d;
exec($com,$out);

foreach($out as $key => $value)
{
  echo $value;
  echo "\n";
}

}


?>




</textarea><br>
IPC Formula:  <input type="text" style="font-family:'Courier New'" id="form" name="form" size="60" value="(((A \/ B) \/ C) -> (A \/ (B \/ C)))" > Depth:
 <input type="text" style="font-family:'Courier New'" id="dep" name="dep" size="12" value="20"><br>

<input type="submit" value="Search for Proof"><br>
</form>






</body></html>

