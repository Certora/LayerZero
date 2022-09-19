certoraRun certora/harness/EndpointHarness.sol \
     --verify EndpointHarness:certora/spec/endpoint.spec \
     --solc solc7.6 \
     --cloud \
     --loop_iter 3 \
     --optimistic_loop \
     --send_only \
     --rule_sanity \
     --settings -optimisticFallback=true \
     --settings -byteMapHashingPrecision=7 \
     --msg "layerZero New"

    #certora/helpers/DummyERC20A.sol \
    #certora/helpers/DummyERC20B.sol \
    #certora/helpers/Library1.sol \
    #certora/helpers/Library2.sol \