import Erdos883SmallCertificate509Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten509_38 :
    (List.ofFn coreChunks509_38).flatten =
      (coreData509.take (coreResources509 38).q).drop 82 := by
  decide +kernel

theorem coreCheck509_38 :
    ∀ c : Fin 1, (coreChunks509_38 c).all
      (coreResourceRowCheck 463 coreData509 (coreResources509 38)) = true := by
  decide +kernel
#print axioms coreFlatten509_38
#print axioms coreCheck509_38
end Erdos883Verified
