
certoraRun contracts/Endpoint.sol  \
    --verify Endpoint:certora/specs/complexity.spec \
    --solc solc7.6 \
    --optimistic_loop \
    --cloud  \
    --msg "Endpoint complexity check"

 