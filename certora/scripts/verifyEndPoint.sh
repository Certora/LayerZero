certoraRun certora/harness/EndpointHarness.sol \
     --verify EndpointHarness:certora/spec/endpoint.spec \
     --solc solc7.6 \
     --staging \
     --optimistic_loop \
     --loop_iter 2 \
     --send_only \
     --rule_sanity basic \
     --rule afterForceCannotRetry \
     --settings -byteMapHashingPrecision=7 \
     --msg "layerZero afterForceCannotRetry"

    #certora/helpers/DummyERC20A.sol \
    #certora/helpers/DummyERC20B.sol \
    #certora/helpers/Library1.sol \
    #certora/helpers/Library2.sol \