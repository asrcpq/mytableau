sed -E 's/\(([^ ]*) /\1(/g' |
	sed 's/NOT/!/g' |
	sed 's/AND/\&/g' |
	sed 's/OR/|/g' |
	sed 's/SOME/#/g' |
	sed 's/ALL/@/g'
