import Erdos883SmallCertificate509Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten509_13 :
    (List.ofFn coreChunks509_13).flatten =
      (coreData509.take (coreResources509 13).q).drop 102 := by
  decide +kernel

theorem coreCheck509_13 :
    ∀ c : Fin 1, (coreChunks509_13 c).all
      (coreResourceRowCheck 463 coreData509 (coreResources509 13)) = true := by
  decide +kernel
#print axioms coreFlatten509_13
#print axioms coreCheck509_13
end Erdos883Verified
