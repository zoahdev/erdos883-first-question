import Erdos883AdaptiveSpan86416Level1TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength86416_1 : adaptiveNumericSpans86416_1.length = 610 := by decide +kernel
theorem adaptiveSpanEvenCache86416_1 : adaptiveSpanEven86416_1.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain86416_1 : adaptiveSpanEven86416_1.domainCheck 43208 = true := by decide +kernel
theorem adaptiveSpanEvenEntries86416_1 : adaptiveSpanEven86416_1.spans = coreEvenSpans 43208 0 adaptiveNumericSpans86416_1 := by
  decide +kernel
theorem adaptiveSpanWholeCache86416_1 : adaptiveSpanWhole86416_1.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain86416_1 : adaptiveSpanWhole86416_1.domainCheck 43208 = true := by decide +kernel
theorem adaptiveSpanWholeEntries86416_1 : adaptiveSpanWhole86416_1.spans = coreWholeSpans 0 adaptiveNumericSpans86416_1 := by
  decide +kernel
end Erdos883Verified
