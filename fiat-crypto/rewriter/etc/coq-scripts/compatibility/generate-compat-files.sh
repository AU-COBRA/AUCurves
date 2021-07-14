#!/bin/bash

function append() {
    SOURCE="$1"
    VERSIONS="$2"
    for v in $VERSIONS; do
	echo >> "Coq__${v}__Compat.v"
	cat "$SOURCE" >> "Coq__${v}__Compat.v"
    done
}

function append_text() {
    TEXT="$1"
    VERSIONS="$2"
    for v in $VERSIONS; do
	echo "$TEXT" >> "Coq__${v}__Compat.v"
    done
}

ALL_VERSIONS="8_4 8_5beta1 8_5beta2 8_5beta3 8_5rc1 8_5 8_5pl1 8_6beta1 8_6 8_7 8_8 8_9 8_10 8_11 8_12 8_13 8_14 trunk master"
VECTOR_LIST_VERSIONS="8_4 8_5beta1 8_5beta2 8_5beta3 8_5rc1 8_5 8_5pl1 8_6beta1 8_6 8_7 8_8 8_9 8_10 8_11 8_12 8_13 8_14 trunk master"
NPEANO_VERSIONS="8_5beta1 8_5beta2 8_5beta3 8_5rc1 8_5 8_5pl1"
FMAPFACTS_VERSIONS="8_5beta1 8_5beta2 8_5beta3 8_5rc1 8_5 8_5pl1"
COQ_MODULE_VERSIONS="8_5beta1 8_5beta2 8_5beta3 8_5rc1 8_5 8_5pl1"
FAST_SET_AS_SET_VERSIONS="8_5beta1 8_5beta2 8_5beta3 8_5rc1 8_5 8_5pl1 8_6beta1 8_6 8_7 8_8 8_9 8_10 8_11 8_12 8_13 8_14 trunk master"
RELATION_ARGUMENTS_VERSIONS="8_5beta1 8_5beta2 8_5beta3 8_5rc1 8_5"
RAPPLY_SHELVE_VERSIONS="8_5beta1 8_5beta2 8_5beta3"
MISC_BETA1_VERSIONS="8_5beta1 8_5beta2"
INT_VERSIONS="8_5beta2"
FUNIND_VERSIONS="8_7 8_8 8_9 8_10 8_11 8_12 8_13 8_14 trunk master"
GRAB_88_VERSIONS="8_9 8_10 8_11"
GRAB_88v811_VERSIONS="8_12"
GRAB_88v813_VERSIONS="8_13"
GRAB_88v814_VERSIONS="8_14 master"

for v in $ALL_VERSIONS; do
    cp -f "Coq__${v}__Compat.v.in" "Coq__${v}__Compat.v"
done
append "fragments/Grab88v811.v" "$GRAB_88v811_VERSIONS"
append "fragments/Grab88v813.v" "$GRAB_88v813_VERSIONS"
append "fragments/Grab88v814.v" "$GRAB_88v814_VERSIONS"
append "fragments/Grab88.v" "$GRAB_88_VERSIONS"
append "fragments/FastSetAsSet.v" "$FAST_SET_AS_SET_VERSIONS"
append "fragments/RelationArguments.v" "$RELATION_ARGUMENTS_VERSIONS"
append "fragments/RapplyShelve.v" "$RAPPLY_SHELVE_VERSIONS"
append "fragments/MiscBeta1.v" "$MISC_BETA1_VERSIONS"
append "fragments/VectorListNotations.v" "$VECTOR_LIST_VERSIONS"
append "fragments/NPeanoRequires.v" "$NPEANO_VERSIONS"
append "fragments/FMapFactsRequires.v" "$FMAPFACTS_VERSIONS"
append "fragments/IntRequires.v" "$INT_VERSIONS"
append_text "Module Export Coq." "$COQ_MODULE_VERSIONS"
append "fragments/NPeanoFixes.v" "$NPEANO_VERSIONS"
append "fragments/FMapFactsFixes.v" "$FMAPFACTS_VERSIONS"
append "fragments/IntFixes.v" "$INT_VERSIONS"
append_text "End Coq." "$COQ_MODULE_VERSIONS"
append_text "Require Export Coq.funind.FunInd." "$FUNIND_VERSIONS"
