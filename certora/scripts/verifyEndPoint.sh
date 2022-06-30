certoraRun contracts/Endpoint.sol \
    certora/helpers/DummyERC20A.sol \
    certora/helpers/DummyERC20B.sol \
    certora/helpers/Library1.sol \
    certora/helpers/Library2.sol \
    contracts/mocks/LayerZeroTokenMock.sol \
    \
    \
     --verify Endpoint:certora/spec/endPoint.spec \
     --link Endpoint:defaultSendLibrary=ULN1 \
     --solc solc8.2 \
     --staging \
     --optimistic_loop \
     --loop_iter 2 \
     --packages_path node_modules \
     --packages @openzeppelin=node_modules/@openzeppelin \
     --msg "Endpoint"