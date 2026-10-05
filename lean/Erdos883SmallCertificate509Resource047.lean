import Erdos883SmallCertificate509Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten509_47 :
    (List.ofFn coreChunks509_47).flatten =
      (coreData509.take (coreResources509 47).q).drop 92 := by
  decide +kernel

theorem coreCheck509_47 :
    ∀ c : Fin 1, (coreChunks509_47 c).all
      (coreResourceRowCheck 463 coreData509 (coreResources509 47)) = true := by
  decide +kernel
#print axioms coreFlatten509_47
#print axioms coreCheck509_47
end Erdos883Verified
