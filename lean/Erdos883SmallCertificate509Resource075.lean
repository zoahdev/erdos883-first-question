import Erdos883SmallCertificate509Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten509_75 :
    (List.ofFn coreChunks509_75).flatten =
      (coreData509.take (coreResources509 75).q).drop 143 := by
  decide +kernel

theorem coreCheck509_75 :
    ∀ c : Fin 1, (coreChunks509_75 c).all
      (coreResourceRowCheck 463 coreData509 (coreResources509 75)) = true := by
  decide +kernel
#print axioms coreFlatten509_75
#print axioms coreCheck509_75
end Erdos883Verified
