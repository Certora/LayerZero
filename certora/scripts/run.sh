
certoraRun contracts/Endpoint.sol  \
    --verify Endpoint:certora/spec/complexity.spec \
    --solc solc7.6 \
    --optimistic_loop \
    --staging  \
    --send_only \
    --msg "Endpoint complexity check"

 