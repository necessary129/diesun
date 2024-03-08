#!/bin/bash
#SBATCH -A research
#SBATCH --qos=medium
#SBATCH -n 20
#SBATCH --mem-per-cpu=3072
#SBATCH --time=3-00:00:00
#SBATCH --mail-type=BEGIN
#SBATCH -o JOB%j.out # File to which STDOUT will be written
#SBATCH -e JOB%j.out # File to which STDERR will be written

set -eu
source $HOME/.bashrc

secs_to_human(){
    echo "$(( ${1} / 3600 )):$(( (${1} / 60) % 60 )):$(( ${1} % 60 ))"
}
start=$(date +%s)
echo "$(date -d @${start} "+%Y-%m-%d %H:%M:%S"): ${SLURM_JOB_NAME} start id=${SLURM_JOB_ID}\n"
(bash fuzz-parallel.sh) \
    && (cat JOB$SLURM_JOB_ID.out |mail -s "$SLURM_JOB_NAME Ended after $(secs_to_human $(($(date +%s) - ${start}))) id=$SLURM_JOB_ID" muhammed.shamil@research.iiit.ac.in && echo mail sended) \
|| (cat JOB$SLURM_JOB_ID.out |mail -s "$SLURM_JOB_NAME Failed after $(secs_to_human $(($(date +%s) - ${start}))) id=$SLURM_JOB_ID" muhammed.shamil@research.iiit.ac.in && echo mail sended && exit $?)

