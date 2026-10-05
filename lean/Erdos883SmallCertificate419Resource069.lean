import Erdos883SmallCertificate419Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten419_69 :
    (List.ofFn coreChunks419_69).flatten =
      (coreData419.take (coreResources419 69).q).drop 163 := by
  decide +kernel

theorem coreCheck419_69 :
    ∀ c : Fin 1, (coreChunks419_69 c).all
      (coreResourceRowCheck 381 coreData419 (coreResources419 69)) = true := by
  decide +kernel
#print axioms coreFlatten419_69
#print axioms coreCheck419_69
end Erdos883Verified
