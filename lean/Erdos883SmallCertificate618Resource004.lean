import Erdos883SmallCertificate618Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten618_4 :
    (List.ofFn coreChunks618_4).flatten =
      (coreData618.take (coreResources618 4).q).drop 73 := by
  decide +kernel

theorem coreCheck618_4 :
    ∀ c : Fin 1, (coreChunks618_4 c).all
      (coreResourceRowCheck 562 coreData618 (coreResources618 4)) = true := by
  decide +kernel
#print axioms coreFlatten618_4
#print axioms coreCheck618_4
end Erdos883Verified
