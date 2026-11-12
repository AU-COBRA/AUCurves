#!/bin/bash
# Prints the rocq load-path flags used for ${JAST_TOOLS:-$HOME/tools}/jast/rocq:
# $JAST_TOOLS/jast/flags.txt (the AUCurves flags) minus the AUCurves -Q/-R entries
# (the leaves term needs only the switch's Stdlib/mathcomp/HB/coqutil/bedrock2/Jasmin),
# plus this directory's two logical roots.
R=${JAST_TOOLS:-$HOME/tools}/jast/rocq
sed -e 's# -Q ${AUCURVES:-$HOME/AUCurves}/[^ ]* [^ ]*##g' -e 's# -R ${AUCURVES:-$HOME/AUCurves}/[^ ]* [^ ]*##g' ${JAST_TOOLS:-$HOME/tools}/jast/flags.txt | tr -d '\n'
echo " -Q $R/JasminBridge/Ast JasminBridge.Ast -Q $R/Bedrock/JasminAst Bedrock.JasminAst"
