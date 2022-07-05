if [[ "$1" ]]
then
    RULE="--rule $1"
fi

certoraRun certora/harness/EndpointHarness.sol \
     --verify EndpointHarness:certora/spec/endpoint.spec \
     --solc solc7.6 \
     --staging \
     --optimistic_loop \
     --loop_iter 2 \
     $RULE  \
     --settings -byteMapHashingPrecision=7 \
     --msg "Endpoint -$RULE"