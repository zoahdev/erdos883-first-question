import Erdos883AdaptiveSpan86416Level4TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength86416_4 : adaptiveNumericSpans86416_4.length = 610 := by decide +kernel
theorem adaptiveSpanEvenCache86416_4 : adaptiveSpanEven86416_4.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain86416_4 : adaptiveSpanEven86416_4.domainCheck 43208 = true := by decide +kernel
theorem adaptiveSpanEvenEntries86416_4 : adaptiveSpanEven86416_4.spans = coreEvenSpans 43208 0 adaptiveNumericSpans86416_4 := by
  decide +kernel
theorem adaptiveSpanWholeCache86416_4 : adaptiveSpanWhole86416_4.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain86416_4 : adaptiveSpanWhole86416_4.domainCheck 43208 = true := by decide +kernel
theorem adaptiveSpanWholeEntries86416_4 : adaptiveSpanWhole86416_4.spans = coreWholeSpans 0 adaptiveNumericSpans86416_4 := by
  decide +kernel
end Erdos883Verified
