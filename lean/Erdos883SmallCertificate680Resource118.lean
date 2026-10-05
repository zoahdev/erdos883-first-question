import Erdos883SmallCertificate680Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten680_118 :
    (List.ofFn coreChunks680_118).flatten =
      (coreData680.take (coreResources680 118).q).drop 281 := by
  decide +kernel

theorem coreCheck680_118 :
    ∀ c : Fin 1, (coreChunks680_118 c).all
      (coreResourceRowCheck 619 coreData680 (coreResources680 118)) = true := by
  decide +kernel
#print axioms coreFlatten680_118
#print axioms coreCheck680_118
end Erdos883Verified
