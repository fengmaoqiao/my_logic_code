use 5.010;
use File::Basename;

my $filename = '/home/my-linux/workplace/Perl_test/in.v';#输入文件名
my $outfilename = '/home/my-linux/workplace/Perl_test/out.v';#输出文件名
my $basename = basename($filename,".v");
#----------------------------------------------------------
#测试文件存在
die "文件$filename不存在！\n" unless -e $filename;
#打开文件
open(VFILE,"<",$filename) || die "打开文件失败!\n";
open(OFILE,">",$outfilename) || die "打开文件失败!\n";
#----------------------------------------------------------
#对文件预处理,begin...end if...else if...begin等在一行的改成两行
#未添加begin...end的always块进行添加
$always_cnt = 0;
my $last_line = "";
while(<VFILE>){
	chomp;#去除行尾的\n
	
	if(/(.*if.*)(begin.*)/i){
		push @content,$1;
		push @content,$2;
		$last_line = $2;
	}
	elsif(/(.*begin.*)(if.*)/i){
		push @content,$1;
		push @content,$2;
		$last_line = $2;
	}
	elsif(/\s*((input|output|reg|wire|(?:output\s+reg))\s*(\[.+\:.+\])?\s*)((?!reg|wire)(?:(\w+)\s*,\s*(\w+)))([,;]?)/){
		#对于单行定义多个变量进行换行处理
		push @content, $1." ".$5.";";
		push @content, $1." ".$6.";";
		$last_line = $2;
	}
	elsif(/^\s*$/){#空行
		#删除空行
		#say $last_line;
	}
	elsif(/always|module|endmodule|assign|initial/i){#匹配到always		
		if($last_line =~ /\s*\S+$/ or $last_line =~ /^$/){
			#上一行不是空格，就添加一个空行
			push @content,"";
		}
		push @content,$_;
		$last_line = $_;
	}
	elsif(/\bif\s*\(/i){#匹配到if
		if($last_line =~ /always/){
			#上一行是always
			$always_cnt = 1;
			push @content,"begin";
		}
		push @content,$_;
		$last_line = $_;
	}
	else{
		push @content,$_;
		$last_line = $_;
	}
}
$always_cnt = 0;
#print join("\n",@content);

#----------------------------------------------------------
#变量定义
$begin_cnt = 0;
$if_cnt = 0;
$autoindent_space = " "x4;#自动缩进的空格数（Tab宽度）
$last_line = "";
$assign_start = 0;
#模块定义开始
$module_def_start = 0;
my $module_cnt = 0;

#==========================================================
#读取并处理文件
#while(<VFILE>){
foreach (@content){
	#print $begin_cnt,$_,"\n";
	$line = $_;
	if($assign_start){
		if(/.*;/){
			$assign_start = 0;
		}
	}
	if(/\s*\b(input|output|reg|wire)\b/i){
		$line =~ s/^\s+//;
		my @result = ($line =~ /\s*(input|output|reg|wire|(?:output\s+reg))\s*(\[.+\:.+\])?\s*((?!reg|wire)\w+)\s*([,;]?)/ig);
		#print length($result[0]),"--@result\n";
		if($#result>0){
			$line = $autoindent_space;
			$line .= $result[0]." "x(20-length($result[0]));
			$line .= $result[1]." "x(20-length($result[1]));
			$line .= $result[2]." "x(20-length($result[2]));
			$line .= $result[3];
			if((my $len = length($result[2]))>20){
				print "变量名过长(实际长度$len>20字符):\t$result[2]\n";
			}
		}
	}
	elsif(/(parameter)?\s*(\w+)\s*\=\s*((?:\d+\'[hbHB][0-9a-fA-F_]+)|(?:\d+))\s*([,;]?)/i){
		$line =~ s/^\s+//;
		my @result = ($line =~ /(parameter)?\s*(\w+)\s*\=\s*((?:\d+\'[hbHB][0-9a-fA-F_]+)|(?:\d+))\s*([,;]?)/ig);
		#print $#result."--@result\n";
		if($#result>0){
			$line = $autoindent_space;
			$line .= $result[0]." "x(20-length($result[0]));
			$line .= $result[1]." "x(35-length($result[1]));
			$line .= "= ".$result[2]." "x(18-length($result[2]));
			$line .= $result[3];
		}
	}	
	elsif(/\s*\b(module|endmodule|assign|initial)\b/i){#匹配到module|always|assign
		$line =~ s/^\s+//;
		if(/\s*\b(assign|initial)\b\s+\w/i){#匹配到assign
			$line =~ s/\s*\b(assign|initial)\b\s+(\w)/$1  $2/i;
			$assign_start = 1;
			#print;
		}
		if(/module\s+(\w+)\s*\(/i){
			#未匹配到分号，表示module输入输出定义多行
			if(!/.*;/){
				$module_def_start = 1;
				$line = "\n//--------------start of module define--------------\n".$line;
			}
			$module_cnt++;
			if($module_cnt>1){
				print "文件存在多个module\n";
			}			
			if($basename ne $1){
				print "module名$1和文件名$basename不一致!\n";
			}
		}		
	}
	elsif(/\bbegin\b/i){#匹配到begin
		my $tmp_space = $autoindent_space x $begin_cnt;
		$begin_cnt++;
		$line =~ s/^\s*/$tmp_space/;
	}
	elsif(/\bend\b/i){#匹配到end
		if($if_cnt>0){
			$if_cnt--;
		}
		my $tmp_space = $autoindent_space x ($begin_cnt-1);
		$begin_cnt>0 && $begin_cnt--;
		$line =~ s/^\s*/$tmp_space/;
	}
	elsif(/if\s*\(/i){#匹配到if
		$if_cnt++;
		my $tmp_space = $autoindent_space x $begin_cnt;
		$line =~ s/^\s*/$tmp_space/;
	}
	elsif(/\belse\s*/i){#匹配到else
		my $tmp_space = $autoindent_space x $begin_cnt;
		$line =~ s/^\s*/$tmp_space/;
	}
	elsif(/always/){
		$always_cnt=1;
		$line =~ s/^\s*/$tmp_space/;
	}
	elsif(/^\s*$/){#匹配到空行
		#say "="x20;
		#always结束的空行（代码中间的空行已经删除）
		if($if_cnt==0 && $begin_cnt==1 && $always_cnt==1){
			#加入always的end
			$line = "end\n";
			$begin_cnt=0;
			$always_cnt=0;
		}
	}
	else{
		if($last_line =~ /(\s+if\s*\()|(\belse\s*)|(^\s*\w+\:\s*)/){#上一行是if/else/case分支
			$if_cnt>0 && $if_cnt--;
			my $tmp_space = $autoindent_space x ($begin_cnt+1);
			$line =~ s/^\s*/$tmp_space/;
		}
		else{
			my $tmp_space = $autoindent_space x $begin_cnt;
			$line =~ s/^\s*/$tmp_space/;
		}
		if($module_def_start)
		{
			if(/.*;/){
				#最后一行module定义
				$line = ($autoindent_space x 4).$line;
				$line .= "\n//--------------end of module define--------------\n";
				$module_def_start = 0;
			}
			else{
				$line = ($autoindent_space x 4).$line;
			}
		}
		if($assign_start){
			#print "*"x5;
			#$always_cnt=0;
			my $tmp_space = $autoindent_space x 2;
			$line =~ s/^\s*/$tmp_space/;
			if(/".*;\s*$"/){
				$assign_start = 0;
			}
			#say $line;
		}
		
	}
	$last_line = $line;
	#say $if_cnt."-".$begin_cnt."-".$always_cnt."--".$line;
	$text.=$line."\n";
}

#关闭文件
close VFILE;
select OFILE;
print $text;
close OFILE;
select STDOUT;
print "-"x40,"\n"."处理完毕，文件输出到$outfilename\n";
