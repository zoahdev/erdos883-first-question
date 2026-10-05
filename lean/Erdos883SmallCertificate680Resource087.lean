import Erdos883SmallCertificate680Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten680_87 :
    (List.ofFn coreChunks680_87).flatten =
      (coreData680.take (coreResources680 87).q).drop 158 := by
  decide +kernel

theorem coreCheck680_87 :
    ∀ c : Fin 1, (coreChunks680_87 c).all
      (coreResourceRowCheck 619 coreData680 (coreResources680 87)) = true := by
  decide +kernel
#print axioms coreFlatten680_87
#print axioms coreCheck680_87
end Erdos883Verified
