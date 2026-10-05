import Erdos883SmallCertificate680Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten680_96 :
    (List.ofFn coreChunks680_96).flatten =
      (coreData680.take (coreResources680 96).q).drop 176 := by
  decide +kernel

theorem coreCheck680_96 :
    ∀ c : Fin 1, (coreChunks680_96 c).all
      (coreResourceRowCheck 619 coreData680 (coreResources680 96)) = true := by
  decide +kernel
#print axioms coreFlatten680_96
#print axioms coreCheck680_96
end Erdos883Verified
