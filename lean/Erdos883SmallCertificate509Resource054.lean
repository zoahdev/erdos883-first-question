import Erdos883SmallCertificate509Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten509_54 :
    (List.ofFn coreChunks509_54).flatten =
      (coreData509.take (coreResources509 54).q).drop 102 := by
  decide +kernel

theorem coreCheck509_54 :
    ∀ c : Fin 1, (coreChunks509_54 c).all
      (coreResourceRowCheck 463 coreData509 (coreResources509 54)) = true := by
  decide +kernel
#print axioms coreFlatten509_54
#print axioms coreCheck509_54
end Erdos883Verified
