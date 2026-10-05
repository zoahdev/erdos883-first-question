import Erdos883SmallCertificate618Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten618_73 :
    (List.ofFn coreChunks618_73).flatten =
      (coreData618.take (coreResources618 73).q).drop 143 := by
  decide +kernel

theorem coreCheck618_73 :
    ∀ c : Fin 1, (coreChunks618_73 c).all
      (coreResourceRowCheck 562 coreData618 (coreResources618 73)) = true := by
  decide +kernel
#print axioms coreFlatten618_73
#print axioms coreCheck618_73
end Erdos883Verified
